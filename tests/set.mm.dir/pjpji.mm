include "pjpj0i.mm"

theorem pjpji
  let cA: class A
  let cH: class H
  assume pjpj.1: |- H e. CH
  assume pjpj.2: |- A e. ~H


  assert |- A = ( ( ( projh ` H ) ` A ) +h ( ( projh ` ( _|_ ` H ) ) ` A ) )

  proof
    cA
    cH
    pjpj.1
    pjpj.2
    pjpj0i
end
