class ProofNode {
    static input (init,calcwidth) {
            var theInput = document.createElement("input")
            if (init) theInput.value = init;
            else theInput.setAttribute("style","width:1ch");
            theInput.setAttribute("style","width:" + calcwidth(theInput) + "ch");
            theInput.addEventListener('input', function () {
                theInput.setAttribute("style","width:" + calcwidth(theInput) + "ch");
            });
            return theInput
        };

    constructor(obj) { 
        this.forest = [];
        this.labelContent = "";
        this.ruleContent = "";
        this.infoContent = "";
        this.class = "";
        this.parentNode = null

        if (obj) {
            this.label = obj.label;
            this.rule = obj.rule;
            if (obj.forest) obj.forest.map(o => {this.addChild(o)})
        };
    }

    renderOn(target) {
        var elt = document.createElement("div");

        var forestElt = document.createElement("div");
        elt.forestElt = forestElt
        forestElt.setAttribute("class","forest");

        elt.addRule = () => {
            var childElt = forestElt.lastChild
                if (childElt) {
                var childLabel = childElt.lastChild
                var ruleContainer = document.createElement("div");
                var ruleInput = ProofNode.input(this.ruleContent, i => {return i.value.length});
                elt.ruleElt = ruleInput;
                ruleContainer.setAttribute("class","rule");
                ruleContainer.appendChild(ruleInput);
                childLabel.removeChild(childLabel.lastChild);
                childLabel.appendChild(ruleContainer);
                ruleInput.value = this.ruleContent;
                ruleInput.addEventListener('input', () => {
                    this.ruleContent = ruleInput.value
                    this.trigger("changed", true, this);
                });
                this.on("infoChanged", (i,c) => {
                    try {
                        try {ruleContainer.popper.destroy()} catch (e) {}
                        var msg = document.createElement("div");
                        var wrapper = document.createElement("div");
                        msg.innerHTML = i;
                        wrapper.setAttribute("class","rulePopper")
                        wrapper.appendChild(msg);
                        ruleContainer.appendChild(wrapper);
                        ruleContainer.setAttribute("class","rule " + c)
                        ruleContainer.popper = new Popper(ruleInput,msg,{
                            placement: "right",
                            removeOnDestroy: true,
                        });
                    } catch(e) {
                        console.log(e)
                        ruleInput.setAttribute("title", i);
                    }
                });
            }
        }

        var theChildElt = this.forest.map(n => {return n.renderOn(forestElt)})[0]

        if (this.forest.length > 0) { elt.addRule() }

        var labelElt = document.createElement("div");
        if (!this.parentNode)  labelElt.setAttribute("class","root") 
        else labelElt.setAttribute("class","label");
        
        var inputElt = ProofNode.input(this.label,i =>{
            if (!this.parentNode) return i.value.length
            else {
                var myShare = this.parentNode.label.length / this.parentNode.forest.length
                return Math.max(i.value.length,myShare)
            }
        })
        this.on("labelChanged", l => {
            if (l != inputElt.value) {
                inputElt.value = l;
                inputElt.dispatchEvent(new Event('input'))
            }
        });
        this.on("siblingsChanged", () => {inputElt.dispatchEvent(new Event('input'))});
        this.on("parentChanged", () => {inputElt.dispatchEvent(new Event('input'))});

        inputElt.addEventListener('keyup', e => {
            if (e.code == "Enter" && e.ctrlKey) {
                e.preventDefault()
                var newNode = this.addChild()
                if (this.forest.length == 1) elt.ruleElt.focus();
                else forestElt.firstChild.inputElt.focus();
            } else if (e.code == "Enter") {
                e.preventDefault();
                var newNode = this.parentNode.addChild();
                elt.parentElement.firstChild.inputElt.focus()
            } else if (e.code == "Backspace" && e.ctrlKey) {
                var parentElt = elt.parentElement.parentElement;
                this.remove()
                parentElt.inputElt.focus()
                this.parentNode.trigger("changed", true, this)
            };
            this.label = inputElt.value
            this.trigger("changed", true, this)
            this.forest.map(n =>{n.trigger("parentChanged")})
        });

        elt.setAttribute("class","node");
        elt.appendChild(forestElt);
        elt.appendChild(labelElt);
        labelElt.appendChild(document.createElement("div"));
        labelElt.appendChild(inputElt);
        labelElt.appendChild(document.createElement("div"));
        elt.inputElt = inputElt;

        this.on("removed", () => { 
            var nodeAbove = elt.parentElement.parentElement
            elt.parentElement.removeChild(elt);
            if (this.parentNode.forest.length > 0) nodeAbove.addRule()
        });

        this.on("newChild", child => { 
            child.renderOn(forestElt)
            if (this.forest.length == 1) elt.addRule() 
        });

        target.prepend(elt);

        return elt
    }

    get info() { return this.infoContent };

    set info(i) { 
        this.infoContent = i;
        this.trigger("infoChanged", false, i, this.class)
    }

    get label() { return this.labelContent };

    set label(l) { 
        this.labelContent = l;
        this.trigger("labelChanged", false, l) 
        this.trigger("changed", true, this);
    };

    get rule() { return this.ruleContent };

    set rule(r) { 
        this.ruleContent = r;
        this.trigger("ruleChanged", false, r)
        this.trigger("changed", true, this);
    };

    addChild(obj) {
        var child = new ProofNode(obj);
        child.parentNode = this;
        this.forest.push(child);
        this.forest.map(n => {n.trigger("siblingsChanged")})
        this.trigger("newChild", false, child);
        this.trigger("changed", true, this);
        return child;
    };

    remove() {
        if (this.parentNode) {
            this.trigger("removed",false);
            this.parentNode.forest.splice(this.parentNode.forest.indexOf(this),1);
            this.parentNode.forest.map(n => {n.trigger("siblingsChanged")})
        }
    };

    toJSON() {
        return {
            label: this.label,
            rule: this.rule,
            forest: this.forest,
        };
    };

    toInfo() {
        return {
            info: this.info,
            class: this.class,
            forest: this.forest.map(t => t.toInfo()),
        };
    };

    decorate(obj) {
        if (typeof(obj.class) != 'undefined') this.class = obj.class;
        if (typeof(obj.info) != 'undefined') this.info = obj.info;
        var i = 0;
        if (typeof(obj.forest) != 'undefined') for (const o of this.forest) {
            if (typeof(obj.forest[i]) != 'undefined') {
                o.decorate(obj.forest[i]);
            }
            i++;
        };
    };

    replace(obj) {
        this.label = obj.label
        this.rule = obj.rule
        this.forest.map(n => {n.remove()});
        obj.forest.map(o => {this.addChild(o)});
    };

    on(eventName, handler) {
      if (!this._eventHandlers) this._eventHandlers = {};
      if (!this._eventHandlers[eventName]) this._eventHandlers[eventName] = [];
      this._eventHandlers[eventName].push(handler);
    };

    off(eventName, handler) {
      let handlers = this._eventHandlers && this._eventHandlers[eventName];
      if (!handlers) return;
      for (let i = 0; i < handlers.length; i++) {
        if (handlers[i] === handler) {
          handlers.splice(i--, 1);
        }
      };
    };

    trigger(eventName, bubble, ...args) {
      if (bubble && this.parentNode) {
          this.parentNode.trigger(eventName, bubble, ...args)
      }
      if (!this._eventHandlers || !this._eventHandlers[eventName]) return;
      this._eventHandlers[eventName].forEach(handler => handler.apply(this, args));
    };
};

class ProofRoot extends ProofNode {
    constructor(obj) {
        super(obj)
    };

    renderOn(target) {
        var elt = super.renderOn(target)
        elt.inputElt.setAttribute("readonly","readonly")
    }
};
