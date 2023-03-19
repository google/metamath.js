include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "cort.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "axpjpj.mm"
include "mp2an.mm"

theorem pjpj0i
  let cA: class A
  let cH: class H
  assume pjcli.1: |- H e. CH
  assume pjcli.2: |- A e. ~H


  assert |- A = ( ( ( projh ` H ) ` A ) +h ( ( projh ` ( _|_ ` H ) ) ` A ) )

  proof
    cH
    cch
    wcel
    cA
    chil
    wcel
    cA
    cA
    cH
    cpjh
    cfv
    cfv
    cA
    cH
    cort
    cfv
    cpjh
    cfv
    cfv
    cva
    co
    wceq
    pjcli.1
    pjcli.2
    cA
    cH
    axpjpj
    mp2an
end
