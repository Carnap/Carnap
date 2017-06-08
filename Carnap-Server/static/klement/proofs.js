
var proofBeingChecked = false;

function processProofCheckResponse(text) {
   // if (!(proofBeingChecked)) {
   //    return;
   // }
   // var res = JSON.parse(text);
   // var restext = '';
   // if (res.issues.length == 0) {
   //    if (res.concReached == true) {
   //       restext += '<span style="font-size: 150%; color: green;">☺</span> Congratulations! This proof is correct.';
   //    } else {
   //       restext += '<span style="font-size: 150%; color: blue;">😐</span> No errors yet, but you haven’t reached the conclusion.';
   //    }
   // } else {
   //    restext += '<span style="font-size: 150%; color: red;">☹</span> <strong>Sorry there were errors</strong>.<br />';
   //    restext += res.issues.join('<br />');
   // }
   proofBeingChecked.results.innerHTML = text;
   proofBeingChecked = false;
}

function maxdepth(prdata) {
   var rv = 0;
   for (var i=0; i<prdata.length; i++) {
      if (Array.isArray(prdata[i])) {
         var newd = (maxdepth(prdata[i]) + 1);
         rv = Math.max(newd,rv);
      }
   }
   return rv;
}

function countnonspacers(rs) {
   var c = 0;
   for (var i=0; i<rs.length; i++) {
      if (!(rs[i].classList.contains("spacerrow"))) {
         c++;
      }
   }
   return c;
}

function dataToRows(prf, prdata, depth, md, ln) {
   var currln = ln;
   var spacerrow = document.createElement("tr");
   spacerrow.classList.add("spacerrow");
   spacerrow.appendChild(document.createElement("td"));
   for (var j=0; j<depth; j++) {
      var c = document.createElement('td');
      spacerrow.appendChild(c);
      c.classList.add('midcell');
   }
   spacerrow.appendChild(document.createElement("td"));
   spacerrow.appendChild(document.createElement("td"));
   var spacercell = document.createElement("td");
   spacerrow.appendChild(spacercell);
   spacercell.classList.add("spacercell");
   var rs=[spacerrow];
   for (var i=0; i<prdata.length; i++) {
      if (Array.isArray(prdata[i])) {
         nrs = dataToRows(prf, prdata[i], (depth+1), md, currln);
         rs = rs.concat(nrs);
         currln += countnonspacers(nrs);
      } else {
         var newrow = document.createElement("tr");
         var rowdata = prdata[i];
         newrow.lineNumCell = document.createElement("td");
         newrow.appendChild(newrow.lineNumCell);
         currln++;
         newrow.ln = currln;
         newrow.myProof = prf;
         newrow.lineNumCell.innerHTML = currln;
         newrow.lineNumCell.classList.add('linenocell');
         for (var j=0; j<depth; j++) {
            var c = document.createElement('td');
            newrow.appendChild(c);
            c.classList.add('midcell');
         }
         newrow.wffCell = document.createElement("td");
         newrow.wffCell.colSpan = ((md - depth) + 1);
         newrow.appendChild(newrow.wffCell);
         newrow.wffCell.classList.add("wffcell");
         if (
            (
               (rowdata.jstr == "Pr") 
               && 
               (
                  ((i+1) == prdata.length)
                  ||
                  (prdata[i+1].jstr != "Pr")
               )
            )
            ||
            ( rowdata.jstr == "Hyp" 
            )
         ) {
            newrow.wffCell.classList.add("sepcell");
         }
         if ((currln != prf.openline) || (prf.jopen) || (rowdata.jstr == "Pr")) {
            newrow.wffDisplay = document.createElement("span");
            newrow.wffCell.appendChild(newrow.wffDisplay);
            newrow.wffDisplay.innerHTML = prettyStr(rowdata.wffstr);
            if (rowdata.jstr != "Pr") {
               newrow.wffCell.myProof = prf;
               newrow.wffCell.myPos = currln;
               newrow.wffCell.title = "click to edit";
               newrow.wffCell.onclick = function() {            
                  this.myProof.registerInput();
                  this.myProof.openline = this.myPos;
                  this.myProof.jopen = false;
                  this.myProof.displayMe();
               } 
            } else {
               newrow.wffCell.classList.add("noclick");
            }
         } else {
            prf.oInput = document.createElement("input");
            newrow.wffCell.appendChild(prf.oInput);
            prf.oInput.title = "Insert formula for this line here.";
            prf.oInput.myPos = (currln - 1);
            prf.oInput.myProof = prf;
            prf.oInput.value = rowdata.wffstr;
            prf.oInput.classList.add("wffinput");
            prf.oInput.onchange = function() {
                  this.value = fixWffInputStr(this.value);
            }
         }
         newrow.jCell = document.createElement("td");
         newrow.appendChild(newrow.jCell);
         newrow.jCell.classList.add("jcell");
         if ((rowdata.jstr != "Hyp") && (rowdata.jstr != "Pr")) {
            if ((currln != prf.openline) || (!(prf.jopen))) {
               newrow.jCell.innerHTML = rowdata.jstr;
               if (rowdata.jstr == "") {
                  newrow.jCell.classList.add("showcell");
               }
               newrow.jCell.myPos = currln;
               newrow.jCell.myProof = prf;
               newrow.jCell.title = "click to edit";
               newrow.jCell.onclick = function() {
                  this.myProof.registerInput();
                  this.myProof.jopen = true;
                  this.myProof.openline = this.myPos;
                  this.myProof.displayMe();
               }
            } else {
               prf.oInput = document.createElement("input");
               newrow.jCell.appendChild(prf.oInput);
               prf.oInput.title = "Insert justification for this line here.";
               prf.oInput.myPos = (currln - 1);
               prf.oInput.myProof = prf;
               prf.oInput.value = rowdata.jstr;
               prf.oInput.classList.add("jinput");
               prf.oInput.onchange = function() {
                  this.value = fixJInputStr(this.value);
               }
            }
         } else {
            newrow.jCell.classList.add("noclick");
         }
         newrow.bCell = document.createElement("td");
         newrow.appendChild(newrow.bCell);
         newrow.bCell.classList.add("buttoncell");
         if ((rowdata.jstr != "Pr") || (newrow.wffCell.classList.contains("sepcell"))) {
            if (rowdata.jstr != "Pr") {
               var dellink = document.createElement("a");
               newrow.bCell.appendChild(dellink);
               dellink.innerHTML = "×";
               dellink.title = "Delete this line.";
               dellink.myPos = (currln - 1);
               dellink.myProof = prf;
               dellink.onclick = function() {
                  this.myProof.registerInput();
                  this.myProof.openline = 0;
                  this.myProof.jopen = false;
                  this.myProof.oInput = {};
                  this.myProof.deleteLine(this.myPos);
                  this.myProof.displayMe();
               }
            }
            var addrowlink = document.createElement("a");
            var addsplink = document.createElement("a");
            newrow.bCell.appendChild(addrowlink);
            newrow.bCell.appendChild(addsplink);
            addrowlink.innerHTML = '<img src="' + klement_new + '" />';
            addsplink.innerHTML = '<img src="' + klement_newsp + '" />';
            addrowlink.myPos = (currln - 1);
            addrowlink.myProof = prf;
            addsplink.myPos = (currln - 1);
            addsplink.myProof = prf;
            addrowlink.title = "Add a line below this one.";
            addsplink.title = "Add a new subproof below this line.";
            addrowlink.onclick = function() {
               this.myProof.registerInput();
               this.myProof.addNewLine(this.myPos);
               this.myProof.displayMe();
            }
            addsplink.onclick = function() {
               this.myProof.registerInput();
               this.myProof.addNewSubProof(this.myPos);
               this.myProof.displayMe();
            }
            if (((i+1) == prdata.length) && (depth > 0)) {
               var addurowlink = document.createElement("a");
               var addusplink = document.createElement("a");
               newrow.bCell.appendChild(addurowlink);
               newrow.bCell.appendChild(addusplink);
               addurowlink.innerHTML = '<img src="' + klement_newb + '" />';
               addusplink.innerHTML = '<img src="' + klement_newspb + '" />';
               addurowlink.myPos = (currln - 1);
               addurowlink.myProof = prf;
               addusplink.myPos = (currln - 1);
               addusplink.myProof = prf;
               addurowlink.title = "Add a new line to the parent of this subproof below.";
               addusplink.title = "Add a new subproof to the parent of this subproof below.";
               addurowlink.onclick = function() {
                  this.myProof.registerInput();
                  this.myProof.addNewUPLine(this.myPos);
                  this.myProof.displayMe();
               }
               addusplink.onclick = function() {
                  this.myProof.registerInput();
                  this.myProof.addNewUPSubProof(this.myPos);
                  this.myProof.displayMe();
               }
            }
         }
         rs.push(newrow);
      }
   }
   return rs;
}

function flat_array(a, dpar) {
   var b=[];
   for (var i=0; i<a.length; i++) {
         if (Array.isArray(a[i])) {
            
            b = b.concat(flat_array(a[i], dpar.concat([i])));
         } else {
            var x = {};
            x.wffstr = a[i].wffstr;            
            x.jstr = a[i].wffstr;            
            x.location = dpar.concat([i]);
            b.push(x);
         }
   }
   return b;
}

function addNLtoPD(pd, n, newsp, uppa) {
   var fa = flat_array(pd, []);
   if ((fa.length > 0) && (n < fa.length)) {
      loc = fa[n].location;
   } else {
      loc = [n];
   }
   return putNewLineAt(pd, loc, newsp, uppa);
}

function putNewLineAt(pd, loc, newsp, uppa) {
   if ((loc.length == 1) || ( (loc.length == 2) && (uppa)  )) {
      if (newsp) {
         pd.splice(loc[0] + 1, 0, [ { "wffstr" : "", "jstr" : "Hyp" } ]); 
      } else {
         pd.splice(loc[0] + 1, 0, { "wffstr" : "", "jstr" : "" }); 
      }
   } else {
      pd[loc[0]] = putNewLineAt(pd[loc[0]], loc.slice(1), newsp, uppa);
   }
   return pd;
}

function changeWffAt(pd, loc, val) {
   if (loc.length == 1) {
      pd[loc[0]].wffstr = fixWffInputStr(val);
   } else {
      pd[loc[0]] = changeWffAt(pd[loc[0]], loc.slice(1), val);
   }
   return pd;
}

function changeWffValue(pd, pos, val) {
   var fa = flat_array(pd, []);
   if (fa.length > 0) {
      loc = fa[pos].location;
   } else {
      loc = [0];
   }   
   return changeWffAt(pd, loc, val);
}

function changeJAt(pd, loc, val) {
   if (loc.length == 1) {
      pd[loc[0]].jstr = fixJInputStr(val);
   } else {
      pd[loc[0]] = changeJAt(pd[loc[0]], loc.slice(1), val);
   }
   return pd;
}

function changeJValue(pd, pos, val) {
   var fa = flat_array(pd, []);
   if (fa.length > 0) {
      loc = fa[pos].location;
   } else {
      loc = [0];
   }   
   return changeJAt(pd, loc, val);
}

function deletePDLine(pd, pos) {
   var fa = flat_array(pd, []);
   if ((fa.length > 0) && (pos < fa.length)) {
      loc = fa[pos].location;
   } else {
      return;
   }
   if ((loc.length > 1) && (loc[(loc.length - 1)] == 0)) {
      if (confirm("Warning: this will delete the entire subproof.\nDelete anyway?")) {  
         loc.pop();
      } else {
         return pd;
      }
   }
   return delLineFromLocation(pd, loc);
}

function delLineFromLocation(pd, loc) {
   if (loc.length == 1) {
      pd.splice(loc[0], 1);
   } else {
      pd[loc[0]] = delLineFromLocation(pd[loc[0]], loc.slice(1));
   }
   return pd;
}

function makeProof(pardiv, pstart, conc) {
   var p = document.createElement("table");
   pardiv.appendChild(p);
   p.classList.add("prooftable");
   p.proofdata = pstart;
   p.numPrems = 0;
   for (var i=0; i<pstart.length; i++) {
      if ((pstart[i].hasOwnProperty("jstr")) && (pstart[i].jstr=="Pr")) {
         p.numPrems++;
      }
   }
   p.wantedConc = conc;
   p.parentDiv = pardiv;
   p.openline = 1;
   p.jopen = false;
   p.oInput = {};
   
   // associated elements
   
   p.buttonDiv = document.createElement("div");
   pardiv.appendChild(p.buttonDiv);
   p.buttonDiv.classList.add("buttondiv");
   
   p.results = document.createElement("div");
   pardiv.appendChild(p.results);
   p.results.classList.add("resultsdiv");
   
   p.checkButton = document.createElement("button");
   p.checkButton.type = "button";
   p.checkButton.innerHTML = "check proof";
   p.checkButton.myP = p;
   pardiv.appendChild(p.checkButton);
   p.checkButton.onclick = function() {
      this.myP.registerInput();
      this.myP.openline = 0;
      this.myP.jopen = false;
      this.myP.oInput = {};
      this.myP.displayMe();
      this.myP.startCheckMe();
   }


   
   p.startOverButton = document.createElement("button");
   p.startOverButton.type = "button";
   p.startOverButton.innerHTML = "start over";
   pardiv.appendChild(p.startOverButton);
   p.startOverButton.start = pstart.slice(0);
   p.startOverButton.myPardiv = pardiv;
   p.startOverButton.conc = conc;
   p.startOverButton.myP = p;
   p.startOverButton.onclick = function() {
      this.myP.parentNode.removeChild(this.myP.checkButton);
      this.myP.parentNode.removeChild(this.myP.startOverButton);
      this.myP.parentNode.removeChild(this.myP.results);
      this.myP.parentNode.removeChild(this.myP.buttonDiv);
      this.myP.parentNode.removeChild(this.myP);
      makeProof(this.myPardiv, this.start, this.conc);
   }
   

   
   
   p.deleteLine = function(n) {
      this.proofdata = deletePDLine(this.proofdata, n);
   }
   p.addNewLine = function(n) {
      this.proofdata = addNLtoPD(this.proofdata, n, false,false);
      this.openline = (n+2);
      this.jopen = false;
   }
   p.addNewSubProof = function(n) {
      this.proofdata = addNLtoPD(this.proofdata, n, true,false);
      this.openline = (n+2);
      this.jopen = false;      
   }
   p.addNewUPLine = function(n) {
      this.proofdata = addNLtoPD(this.proofdata, n, false,true);
      this.openline = (n+2);
      this.jopen = false;
   }
   p.addNewUPSubProof = function(n) {
      this.proofdata = addNLtoPD(this.proofdata, n, true,true);
      this.openline = (n+2);
      this.jopen = false;      
   }
   p.registerWff = function(pos, val) {
      this.proofdata = changeWffValue(this.proofdata, pos, val);
   }
   p.registerJ = function(pos, val) {
      this.proofdata = changeJValue(this.proofdata, pos, val);
   }
   p.registerInput = function() {
      if (!(this.oInput.tagName == "INPUT")) {
         return;
      }
      if (this.oInput.classList.contains("wffinput")) {
         this.registerWff(this.oInput.myPos, this.oInput.value);
      }
      if (this.oInput.classList.contains("jinput")) {
         this.registerJ(this.oInput.myPos, this.oInput.value);
      }
   }
   
   p.startCheckMe = function() {
      proofBeingChecked = this;
      var transmission = new Object();
      transmission.predicateSettings = predicateSettings;
      transmission.proofData = this.proofdata;
      transmission.wantedConclusion = this.wantedConc;
      transmission.numPrems = this.numPrems;
      acceptJSONCallback_ ( JSON.stringify(transmission)
                          , function(result) { processProofCheckResponse(result); }
                          , function (feedback) { console.log(feedback); });
   }
   
   p.displayMe = function() {
      this.innerHTML = '';
      var md = maxdepth(this.proofdata);
      var rs = dataToRows(this, this.proofdata, 0, md, 0);
      for (var i=0; i< rs.length; i++) {
         this.appendChild(rs[i]);
      }
      var tds = this.getElementsByTagName("td");
      var lasttd = tds[tds.length -1];
      this.buttonDiv.innerHTML = '';
      var bts=lasttd.getElementsByTagName("a");
      for (var i=0; i<bts.length; i++) {
         var b = bts[i];
         var imgs = b.getElementsByTagName("img");
         if (imgs.length > 0) {
            var a=document.createElement("button");
            a.type = "button";
            var im=document.createElement("img");
            im.src = imgs[0].src;
            var sp=document.createElement("span");
            console.log(im.src);
            if (im.src.match(klement_new)) {
               sp.innerHTML = "new line";
               a.title = "Add a new line at end.";
            }
            if (im.src.match(klement_newsp)) {
               sp.innerHTML = "new subproof";
               a.title = "Start a new subproof at end.";
            }
            if (im.src.match(klement_newb)) {
               sp.innerHTML = "finish subproof; add line";
               a.title = "Finish this subproof, and add a line to parent.";
            }
            if (im.src.match(klement_newbsp)) {
               sp.innerHTML = "finish subproof; start another";
               a.title = "Finish this subproof, and add start a new one in parent.";
            }

            this.buttonDiv.appendChild(a);
            a.appendChild(im);
            a.appendChild(sp);
            a.myProof = bts[i].myProof;
            a.myPos = bts[i].myPos;
            a.onclick = bts[i].onclick;
         }
      }
      if (this.buttonDiv.getElementsByTagName("button").length == 0) {
         var a=document.createElement("button");
         a.type = "button";
         this.buttonDiv.appendChild(a);
         a.innerHTML = '<img src="' + klement_new + '" /><span>new line</span>';
         a.title = 'Add a new line.';
         a.myProof = this;
         a.onclick = function() {
            this.myProof.addNewLine(0);
            this.myProof.openline = 1;
            this.myProof.displayMe();
         };
         var b=document.createElement("button");
         b.type = "button";
         this.buttonDiv.appendChild(b);
         b.innerHTML = '<img src="' + klement_newsp + '" /><span>new subproof</span>';
         b.title = 'Add a new subproof.';
         b.myProof = this;
         b.onclick = function() {
            this.myProof.addNewSubProof(0);
            this.myProof.openline = 1;
            this.myProof.displayMe();
         };
      }
      
      try { this.oInput.focus(); } catch(err) { };
   }
   /*if (pstart.length == 0)  {
      p.proofdata = [ { "wffstr" : "", "jstr" : "" } ];
   }*/
   p.displayMe();
   return p;
}
