// The onkeypress event handler is called to:
// (1) allow digits only in INPUT fields
// (2) allow Enter, Backspace, etc in INPUT fields

function keypressHandler(e,id) {
 var chrTyped, chrCode=0, tgt='', evt=e?e:event;
 if (evt.charCode!=null)     chrCode = evt.charCode;
 else if (evt.which!=null)   chrCode = evt.which;
 else if (evt.keyCode!=null) chrCode = evt.keyCode;

 if (chrCode==0) chrTyped = 'SPECIAL KEY';
 else chrTyped = String.fromCharCode(chrCode);

 if ( evt.target   && evt.target.tagName ) tgt = evt.target.tagName.toLowerCase();
 else if ( evt.srcElement && evt.srcElement.tagName) tgt = evt.srcElement.tagName.toLowerCase();

 if ( tgt=="input" || tgt=="textarea")   
 {
  //Digits, special keys & backspace [\b] work as usual:
  if (chrTyped.match(/\d|[\b]|\-|SPECIAL/)) return true;
  if (evt.altKey || evt.ctrlKey || chrCode<21) return true;

  //Any other input? Prevent the default response:
  if (evt.preventDefault) evt.preventDefault();
  evt.returnValue=false;
  return false;
 }
 return true;
}


// keydownHandler disallows Backspace when not using an INPUT or TEXTAREA field

function keydownHandler(e) {
 var elem, tgt='', evt = e ? e:event;
 if (evt.srcElement)  elem = evt.srcElement;
 else if (evt.target) elem = evt.target;
 tgt = elem.tagName.toString().toLowerCase();

 // Cancel BACKSPACE (keyCode 8) as navigation key! 
 if (evt.keyCode==8 && tgt!='input' && tgt!='textarea') return false;  
 return true;
}

document.onkeydown=keydownHandler;
