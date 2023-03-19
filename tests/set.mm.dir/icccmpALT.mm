include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ccmp.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
include "cbnd.mm"
include "cicc.mm"
include "co.mm"
include "icccld.mm"
include "syl5eqel.mm"
include "iccbnd.mm"
include "wss.mm"
include "wb.mm"
include "iccssre.mm"
include "syl5eqss.mm"
include "eqid.mm"
include "reheibor.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem icccmpALT
  let cA: class A
  let cB: class B
  let cT: class T
  let cJ: class J
  let cM: class M
  assume icccmpALT.1: |- J = ( A [,] B )
  assume icccmpALT.2: |- M = ( ( abs o. - ) |` ( J X. J ) )
  assume icccmpALT.3: |- T = ( MetOpen ` M )


  assert |- ( ( A e. RR /\ B e. RR ) -> T e. Comp )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cT
    ccmp
    wcel
    #
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    wcel
    #
    cM
    cJ
    cbnd
    cfv
    wcel
    #
    @0
    cJ
    cA
    cB
    cicc
    co
    #
    @3
    icccmpALT.1
    cA
    cB
    icccld
    syl5eqel
    cA
    cB
    cJ
    cM
    icccmpALT.1
    icccmpALT.2
    iccbnd
    @0
    cJ
    cr
    wss
    @1
    @4
    @5
    wa
    wb
    @0
    cJ
    @6
    cr
    icccmpALT.1
    cA
    cB
    iccssre
    syl5eqss
    cT
    @2
    cM
    cJ
    icccmpALT.2
    icccmpALT.3
    @2
    eqid
    reheibor
    syl
    mpbir2and
end
