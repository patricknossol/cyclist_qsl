fields: next;
precondition: current=zero * x=zero * zero->one * one->two * two->three * three->four * four->five * FALSE->false' * TRUE->true' * break=FALSE;
property: AF(AG(x=one));
while break=FALSE do
  if current=five then
    break:=TRUE
  else
    if * then
      current:=current.next
    else
      current:=five
    fi
  fi
od;
while TRUE=TRUE do
  if * then
    x:=one
  else
    x:=zero
  fi
od;
while TRUE=TRUE do
  skip
od
