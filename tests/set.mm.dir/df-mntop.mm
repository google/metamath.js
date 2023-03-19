
axiom df-mntop
  let vj: setvar j
  let vn: setvar n
  assert |- ManTop = { <. n , j >. | ( n e. NN0 /\ ( j e. 2ndc /\ j e. Haus /\ j e. Locally [ ( TopOpen ` ( EEhil ` n ) ) ] ~= ) ) }
end
