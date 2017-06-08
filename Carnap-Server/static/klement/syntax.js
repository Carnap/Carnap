var predicateSettings=false;

function prettyStr(s) {
   var ps = s;
   ps = ps.replace(/\s*¬\s*/g,'¬');
   ps = ps.replace(/\s*∨\s*/g,' ∨ ');
   ps = ps.replace(/\s*→\s*/g,' → ');
   ps = ps.replace(/\s*↔\s*/g,' ↔ ');
   ps = ps.replace(/\s*∧\s*/g,' ∧ ');
   ps = ps.replace(/\s*=\s*/g,' = ');
   ps = ps.replace(/([A-Za-z]*)/g, '<var>$1</var>');
   return ps;
}

function symReplaceNN(s) {
   var fs = s;
   fs = fs.replace(/<[-−]*>/g,'↔');
   fs = fs.replace(/[-−]*>/g,'→');
   fs = fs.replace(/&/g,'∧');
   fs = fs.replace(/\^/g,'∧');
   fs = fs.replace(/\./g,'∧');
   fs = fs.replace(/\*/g,'∧');
   fs = fs.replace(/·/g,'∧');
   fs = fs.replace(/v/g,'∨');
   if (!(predicateSettings)) {
      fs = fs.replace(/=/g,'↔');
   }
   fs = fs.replace(/≡/g,'↔');
   fs = fs.replace(/⊃/g,'→');
   fs = fs.replace(/⇒/g,'→');
   fs = fs.replace(/XX/g,'⊥');
   fs = fs.replace(/#/g,'⊥');
   if (predicateSettings) {
      fs = fs.replace(/\([A∀⋀]([x-z])\)/g,"∀$1");
      fs = fs.replace(/\([E∃⋁]([x-z])\)/g,"∃$1");
      fs = fs.replace(/[E⋁]([x-z])/g,"∃$1");
      fs = fs.replace(/[A⋀]([x-z])/g,"∀$1");
      fs = fs.replace(/\(([x-z])\)/g,"∀$1");
   }
   return fs;
}

function negReplace(s) {
   var fs = s;
   fs = fs.replace(/~/g,'¬');
   fs = fs.replace(/∼/g,'¬');
   fs = fs.replace(/−/g,'¬');
   fs = fs.replace(/-/g,'¬');     
   return fs;
}

function symReplace(s) {
   return negReplace(symReplaceNN(s));
}

function fixWffInputStr(s) {
   var fs = symReplace(s);
   fs = fs.replace(/  */g, ' ');
   fs = fs.replace(/^\s*/,'');
   fs = fs.replace(/\s*$/,'');
   return fs;
}

function fixJInputStr(s) {
   var fs = symReplaceNN(s);
   fs = fs.replace(/\s*,,*\s*/g, ', ');
   fs = fs.replace(/\s*[-−–][-−–]*\s*/g, '–');
   fs = negReplace(fs);
   fs = fs.replace(/e/g,'E');
   fs = fs.replace(/i/g,'I');
   fs = fs.replace(/  */g, ' ');
   fs = fs.replace(/([∀∃¬∨∧→↔⊥=]) ([EI])/g, "$1$2");
   fs = fs.replace(/[Tt][Nn][Dd]/g, "TND");
   fs = fs.replace(/[Mm][Tt]/g, "MT");
   fs = fs.replace(/[Cc][Qq]/g, "CQ");
   fs = fs.replace(/[Dd][Ss]/g, "DS");
   fs = fs.replace(/[Dd][Nn][Ee]/g, "DNE");
   fs = fs.replace(/[Dd][Ee][Mm]/g, "DeM");
   fs = fs.replace(/EE/g, "∃E");
   fs = fs.replace(/AE/g, "∀E");
   fs = fs.replace(/EI/g, "∃I");
   fs = fs.replace(/AI/g, "∀I");
   fs = fs.replace(/r/g, "R");
   fs = fs.replace(/[Pp][Rr]/g, "");
   fs = fs.replace(/[Hh][Yy][Pp]/g, "");
   fs = fs.replace(/([^\s,0-9–-])([0-9])/g,"$1 $2")
   fs = fs.replace(/([0-9])([^\s,0-9–-])/g,"$1 $2")
   fs = fs.replace(/^[,\s]*/,'');
   fs = fs.replace(/[,\s]*$/,'');
   return fs;
}


function hasStrayChars(s) {
    if (predicateSettings) {
       if (s.match(/[^A-Za-z∀∃=¬∨∧↔→⊥\s\)\(\]\[\}\{]/)) {
          return true;
       } 
    } else {
       if (s.match(/[^A-Z¬∨∧↔→⊥\s\)\(\]\[\}\{]/)) {
          return true;
       } 
    }
    return false;
}

function regularizeMe(s) {
    s=s.replace(/\[/g,'(');
    s=s.replace(/\{/g,'(');
    s=s.replace(/\]/g,')');
    s=s.replace(/\}/g,')');
    s=s.replace(/\s/g,'');
    return s;
}
/* function fixNotation(s, autoUpperCase) {
    s = s.replace(/v/g,'∨');
    if (autoUpperCase) {
        s = s.toUpperCase();
    }
    s = s.replace(/¬/g,'~');
    s = s.replace(/∼/g,'~');
    s = s.replace(/⊃/g,'→');
    s = s.replace(/⇒/g,'→');
    s = s.replace(/≡/g,'↔');
    s = s.replace(/⇔/g,'↔');
    s = s.replace(/\^/g,'&');
    s = s.replace(/∧/g,'&');
    s = s.replace(/∙/g,'&');
    s = s.replace(/\./g,'&');
    s = s.replace(/<-*>/g,'↔');
    s = s.replace(/<=*>/g,'↔');
    s = s.replace(/==*>/g,'→');
    s = s.replace(/-*>/g,'→');
    s = s.replace(/=/g,'↔');
    s = s.replace(/-/g,'~');
    s = s.replace(/\#/g,'✖');
    s = s.replace(/XX/,"✖");
    s = s.replace(/×/g,"✖");
    s = s.replace(/⨳/g,"✖");
    if (predicateSettings) {
        s = s.replace(/A/g,"∀");
        s = s.replace(/E/g,"∃");
        s = s.replace(/\(∀*([xyz])\)/g,"∀$1");
        s = s.replace(/\(∃([xyz])\)/g,"∃$1");
    }
    return s;
} */

function listUnion(z,x) {
    var y=z;
    for (var i=0; i<x.length; i++) {
        if (y.indexOf(x[i]) == -1) {
            y.push(x[i]);
        }
    }
    return y;
}

function wffToStringAndDepth(w) {
    var r='';
    var d=0;
    if (w.wffType=="splat") {
        r='⊥';
        return { stringpart: r,
                 depthpart : d};
    }
    if (w.wffType=="identity") {
       r = w.myTerms[0] + ' = ' + w.myTerms[1];
       return {
          stringpart : r,
          depthpart: d
       };
    }
    if (w.wffType=="atomic") {
       r=w.myLetter;
       if (predicateSettings) {
          r += w.myTerms.join('');
       } 
       return { stringpart: r ,
                 depthpart: d };
    }
    var rightResult=wffToStringAndDepth(w.rightSide);
    var rightAdd=rightResult.stringpart;
    var rightDepth=rightResult.depthpart;
    if (isBinOp(w.rightSide.mainOp)) {
        switch(rightDepth%2) {
            case 0:
                rightAdd='(' + rightAdd + ')';
                break;
            case 1:
                rightAdd='[' + rightAdd + ']';
                break;
        }
        rightDepth += 1;
    }
    if (w.wffType=="quantified") {
        r=w.mainOp + w.myLetter;      
        r+=rightAdd;
        d=rightDepth;
        return { stringpart: r,
                 depthpart: d};
    }
    if (w.mainOp=="¬") {
        r="¬" + rightAdd;
        d=rightDepth;
        return { stringpart: r ,
                 depthpart: d };
    }
    var leftResult=wffToStringAndDepth(w.leftSide);
    var leftAdd=leftResult.stringpart;
    var leftDepth=leftResult.depthpart;
    if (isBinOp(w.leftSide.mainOp)) {
        switch(leftDepth%2) {
            case 0:
                leftAdd='(' + leftAdd + ')';
                break;
            case 1:
                leftAdd='[' + leftAdd + ']';
                break;
        }
        leftDepth += 1;
    }
    d=Math.max(rightDepth,leftDepth);
    r=leftAdd + " " + w.mainOp + " " + rightAdd;
    return { stringpart: r ,
                 depthpart: d };
}

function wffToString(w, makePretty) {
   if (typeof makePretty === "undefined") makePretty = true;
   var rv = wffToStringAndDepth(w).stringpart;
   if (makePretty) {
      rv = prettyStr(rv);
   }
   return rv;
}

function isBinOp(ch) {
    if ((ch=='→') || (ch=='∨') || (ch=='∧') || (ch=='↔')) {
        return true;
    }
    return false;
}

function isMonOp(ch) {
    return ((ch=="¬") || (ch=="∀") || (ch=="∃"));
}

function isOp(ch) {
    return ((isBinOp(ch))||(isMonOp(ch)));
}

function isQuantifier(ch) {
    return ((ch=="∀") || (ch=="∃"));
}

function isVar(ch) {
    return ((ch=="x") || (ch=="y") || (ch=="z"));
}

function getStLtrs(w) {
    var mL=[];
    if (w.wffType=="splat") {
        return mL;
    }
    if (w.wffType=="atomic") {
       mL=[w.myLetter];
       return mL;
    }
    if (w.mainOp=="¬") {
        mL=getStLtrs(w.rightSide);
        return mL;
    }
    mL = getStLtrs(w.leftSide);
    x = getStLtrs(w.rightSide);
    mL = listUnion(mL,x);
    return mL;
}

function newSLWff() {
    return {
        isWellFormed : true,
        ErrMsg : "none",
        wffType : 'unknown',
        mainOp : '?',
        myLetter : '',
        leftSide : {},
        rightSide : {},
    }
}
function newPLWff() {
    return {
        isWellFormed : true,
        ErrMsg : "none",
        wffType : 'unknown',
        mainOp : '?',
        myLetter : '',
        leftSide : {},
        rightSide : {},
        myTerms : [],
        allFreeVars : []
    }
}

// parse string to wff
function parseIt(s) {
    if (predicateSettings) {
       var wff = newPLWff();
    } else {
       var wff = newSLWff();
    }
    var mainOpPos;
    var depthArray=[];
    s=regularizeMe(s);
    // Check if non-empty 
    if (s=='') {
        wff.isWellFormed=false;
        wff.ErrMsg="Formula or subformula is blank."
        return wff;
    }
   // check for stray characters
    if (hasStrayChars(s)) {
            wff.isWellFormed=false;
            if (predicateSettings) {
               wff.ErrMsg="Input field contains characters or punctuation not allowed in the language of FOL. A statement should contain only parentheses ( [ { } ] ), predicates A–Z and =, terms a–w, variables x–z, the contradiction symbol ⊥, and the operators ¬, ∨, ∧, →, ↔, ∃, ∀ (or their alternatives).";
            } else {
               wff.ErrMsg="Input field contains characters or punctuation not allowed in the language of TFL. A statement should contain only parentheses ( [ { } ] ), statement letters A–Z, the contradiction symbol ⊥, and the operators ¬, ∨, ∧, →, and ↔ (or their alternatives).";
            }
            return wff;
    }
    // Check depths and parentheses balance
    var d=0;
    for (var i=0; i<s.length; i++) {
        if (s.charAt(i)=='(') {
            d++;
        }
        if (s.charAt(i)==')') {
            d-=1;
        }
        depthArray[i]=d;
    }
    if (depthArray[s.length-1] != 0) {
        wff.isWellFormed=false;
        wff.ErrMsg="Parentheses are unbalanced.";
        return wff;
    }
    // remove matching outermost parentheses
    if (depthArray[0]==1) {
        var theyMatch=true;
        for (var i=1; i<s.length-1; i++) {
            theyMatch=((theyMatch) && (depthArray[i]>0));
        }
        if (theyMatch) {
            return parseIt(s.substring(1,s.length - 1)); 
        }
    }
    // check if in atomic family
    if (!(s.match(/[¬∧∨→↔∀∃]/))) {
       // should be in atomic family
       
       // should not contain parentheses
       if (s.match(/[\(\)]/)) {
          wff.isWellFormed = false;
          wff.ErrMsg = "Misplaced parentheses.";
          return wff;
       }
       
       // check if splat 
       if (s=="⊥") {
          wff.wffType="splat";
          return wff;
       }
       
       // if still contains splat, that is no good
       if (s.match(/⊥/)) {
          wff.isWellFormed=false;
          wff.ErrMsg = "Formula contains ⊥ but not in isolation.";
          return wff;
       }
       
       // check for identity statement
       if (s.match(/=/)) {
          if (s.match(/^[a-z]=[a-z]$/)) {
             wff.wffType='identity';
             wff.myTerms=s.split("=");
             for (var i=1; i<s.length; i++) {
                if ((isVar(s.charAt(i)) && (wff.allFreeVars.indexOf(s.charAt(i))==-1))) {
                   wff.allFreeVars.push(s.charAt(i))
                }   
             }       
             return wff;
          } else {
             wff.isWellFormed = false;
             wff.ErrMsg = "Poorly formed identity statement. Identity statement should be of the form <var>t</var> = <var>s</var>.";
             return wff;
          }
       }
       
       // check for sentential atomic
       if (!(predicateSettings)) {
          if (s.match(/^[A-Z]$/)) {
             wff.wffType = "atomic";
             wff.myLetter = s;
             return wff;
          } else {
             wff.isWellFormed = false;
             wff.ErrMsg = "Poorly formed atomic statement. In TFL, an atomic statement should be a single statement letter.";
             return wff;
          }
       }
       
       // should be predicate atomic
       
       
       
       if (!(s.charAt(0).match(/[A-Z]/))) {
          wff.isWellFormed=false;
          wff.ErrMsg="An atomic formula must begin with a predicate.";
          return wff;
       }
       if (s.length == 1) {
          wff.isWellFormed = false;
          wff.ErrMsg="An atomic formula must have terms, not just a predicate.";
          return wff;
       }
       if (s.substring(1).match(/[A-Z]/)) {
          wff.isWellFormed=false;
          wff.ErrMsg="Predicates may only appear at the beginning of an atomic formula.";
          return wff;
       }
       if (s.substring(1).match(/[^a-z]/)) {
          wff.isWellFormed=false;
          wff.ErrMsg="An atomic formula should contain only predicates followed by terms.";
          return wff;
       }
       wff.wffType='atomic';
       wff.myLetter=s.charAt(0);
       wff.myTerms=s.substring(1).split("");
       for (var i=1; i<s.length; i++) {
          if ((isVar(s.charAt(i)) && (wff.allFreeVars.indexOf(s.charAt(i))==-1))) {
             wff.allFreeVars.push(s.charAt(i))
          }   
       }
       return wff;
    }
       
       
    /* find main operator */
    for (var i=0; i<s.length; i++) {
        c=s.charAt(i);
        if ((isOp(c)) && (depthArray[i]==0)) {
            if (wff.mainOp=='?') {
                wff.mainOp=c;
                mainOpPos=i;
            } else {
                if ((isBinOp(wff.mainOp)) && (isBinOp(c))) {
                    wff.isWellFormed=false;
                    wff.ErrMsg="Too many operators or too few parentheses to disambiguate.";
                    return wff;
                } else {
                    if ((isMonOp(wff.mainOp)) && (isBinOp(c))) {
                        wff.mainOp=c;
                        mainOpPos=i;
                    }
                }
            }
        }
    }
    /* if no operator found, return an error */
    if (wff.mainOp=='?') {
        wff.isWellFormed=false;
        wff.ErrMsg="Missing connective/operator or misplaced parentheses.";
        return wff;
    }
    if (isQuantifier(wff.mainOp)) {
        /* quantified wff*/
        wff.wffType="quantified";
        /* quantifier must come first */
        if (mainOpPos != 0) {
            wff.isWellFormed=false;
            wff.ErrMsg="Misuse of a quantifier internally in a formula.";
            return wff;
        }
        /* variable must be next */
        if (!(isVar(s.charAt(1)))) {
            wff.isWellFormed=false;
            wff.ErrMsg="A quantifier is used without binding a variable.";
        }
        wff.myLetter=s.charAt(1);
        /* what comes after quantifier must be well-formed */
        wff.rightSide=parseIt(s.substring(2));
        if (!(wff.rightSide.isWellFormed)) {
            wff.isWellFormed=false;
            wff.ErrMsg=wff.rightSide.ErrMsg;
            return wff;
        }
        wff.myTerms=listUnion([],wff.rightSide.myTerms);
        if (wff.myTerms.indexOf(wff.myLetter)==-1) {
            wff.myTerms.push(wff.myLetter);
        } 
        wff.allFreeVars=wff.rightSide.allFreeVars;
        if (wff.allFreeVars.indexOf(wff.myLetter)!=-1) {
            var newFreeVars=[];
            var nfsctr=0;
            for (var k=0; k<wff.allFreeVars.length; k++) {
                if (wff.allFreeVars[k] != wff.myLetter) {
                    newFreeVars[nfsctr]=wff.allFreeVars[k];
                    nfsctr++;
                }
            }
            wff.allFreeVars=newFreeVars;
        }
        return wff;
    }   
    wff.wffType="molecular";
    if (wff.mainOp=="¬") {
        /* main op of negation must be at start, applied to wff */
        if (mainOpPos != 0) {
            wff.isWellFormed=false;
            wff.ErrMsg="Misuse of negation internally in formula.";
            return wff;
        }
        wff.rightSide=parseIt(s.substring(1));
        if (wff.rightSide.isWellFormed==false) {
            wff.isWellFormed=false;
            wff.ErrMsg=wff.rightSide.ErrMsg;
            return wff;
        }
       if (predicateSettings) {
          wff.myTerms=listUnion([],wff.rightSide.myTerms);
          wff.allFreeVars=wff.rightSide.allFreeVars;
       }
        return wff;
    }
    /* two sides of binary molecular wff must be wffs */
    wff.leftSide=parseIt(s.substring(0,mainOpPos));
    wff.rightSide=parseIt(s.substring(mainOpPos+1));
    if (wff.leftSide.isWellFormed==false) {
        wff.isWellFormed=false;
        wff.ErrMsg=wff.leftSide.ErrMsg;
        return wff;
    }
    if (wff.rightSide.isWellFormed==false) {
        wff.isWellFormed=false;
        wff.ErrMsg=wff.rightSide.ErrMsg;
        return wff;
    }
    if (predicateSettings) {
       wff.myTerms=listUnion([],wff.leftSide.myTerms);
       wff.myTerms=listUnion(wff.myTerms,wff.rightSide.myTerms);
       wff.allFreeVars=listUnion(wff.leftSide.allFreeVars,wff.rightSide.allFreeVars);
    }
    return wff;
}


function subTerm(w,n,v) {
    if (w.allFreeVars.indexOf(v) == -1) {
        return w;
    }
    var x=newPLWff();
    x.wffType=w.wffType;
    x.mainOp=w.mainOp;
    x.myLetter=w.myLetter;
    var nfvs=0;
    for (var k=0; k<w.allFreeVars.length; k++) {
        if (w.allFreeVars[k]!=v) {
            x.allFreeVars[nfvs]=w.allFreeVars[k];
            nfvs++;
        }
    }
    if (w.wffType=="atomic") {
        for (var k=0; k<w.myTerms.length; k++) {
            if (w.myTerms[k]==v) {
                x.myTerms[k]=n;
            } else {
                x.myTerms[k]=w.myTerms[k];
            }
        }
        return x;
    }
    x.rightSide=subTerm(w.rightSide,n,v);
    x.myTerms=listUnion([],x.rightSide.myTerms);
    if (isMonOp(x.mainOp)) {
        return x;
    }
    x.leftSide=subTerm(w.leftSide,n,v);
    x.myTerms=listUnion(x.myTerms,x.leftSide.myTerms);
    return x;
}

