
axiom df-xneg
  let cA: class A
  assert |- -e A = if ( A = +oo , -oo , if ( A = -oo , +oo , -u A ) )
end
