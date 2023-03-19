include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "ccl.mm"
include "cfv.mm"
include "cdif.mm"
include "cnt.mm"
include "cin.mm"
include "difundi.mm"
include "fveq2i.mm"
include "wceq.mm"
include "difss.mm"
include "ntrin.mm"
include "mp3an23.mm"
include "3ad2ant1.mm"
include "syl5eq.mm"
include "simp1.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "3adant1.mm"
include "ntrdif.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3adant2.mm"
include "ineq12d.mm"
include "syl6eqr.mm"
include "3eqtr3d.mm"
include "difeq2d.mm"
include "ccld.mm"
include "clscld.mm"
include "cldss.mm"
include "syl.mm"
include "dfss4.mm"
include "sylib.mm"
include "clsss3.mm"
include "jca.mm"
include "bitri.mm"

theorem clsun
  let cA: class A
  let cB: class B
  let cJ: class J
  let cX: class X
  assume clsun.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X /\ B C_ X ) -> ( ( cls ` J ) ` ( A u. B ) ) = ( ( ( cls ` J ) ` A ) u. ( ( cls ` J ) ` B ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    cB
    cX
    wss
    #
    w3a
    #
    cX
    cX
    cA
    cB
    cun
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cdif
    #
    cdif
    #
    cX
    cX
    cA
    @5
    cfv
    #
    cB
    @5
    cfv
    #
    cun
    #
    cdif
    #
    cdif
    #
    @6
    @11
    @3
    @7
    @12
    cX
    @3
    cX
    @4
    cdif
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    cX
    cA
    cdif
    #
    @15
    cfv
    #
    cX
    cB
    cdif
    #
    @15
    cfv
    #
    cin
    #
    @7
    @12
    @3
    @16
    @17
    @19
    cin
    #
    @15
    cfv
    #
    @21
    @14
    @22
    @15
    cX
    cA
    cB
    difundi
    fveq2i
    @0
    @1
    @23
    @21
    wceq
    #
    @2
    @0
    @17
    cX
    wss
    @19
    cX
    wss
    @24
    cX
    cA
    difss
    cX
    cB
    difss
    @17
    @19
    cJ
    cX
    clsun.1
    ntrin
    mp3an23
    3ad2ant1
    syl5eq
    @3
    @0
    @4
    cX
    wss
    #
    @16
    @7
    wceq
    @0
    @1
    @2
    simp1
    #
    @1
    @2
    @25
    @0
    @1
    @2
    wa
    @25
    cA
    cB
    cX
    unss
    biimpi
    3adant1
    #
    @4
    cJ
    cX
    clsun.1
    ntrdif
    syl2anc
    @3
    @21
    cX
    @9
    cdif
    #
    cX
    @10
    cdif
    #
    cin
    @12
    @3
    @18
    @28
    @20
    @29
    @0
    @1
    @18
    @28
    wceq
    @2
    cA
    cJ
    cX
    clsun.1
    ntrdif
    3adant3
    @0
    @2
    @20
    @29
    wceq
    @1
    cB
    cJ
    cX
    clsun.1
    ntrdif
    3adant2
    ineq12d
    cX
    @9
    @10
    difundi
    syl6eqr
    3eqtr3d
    difeq2d
    @3
    @6
    cX
    wss
    #
    @8
    @6
    wceq
    @3
    @6
    cJ
    ccld
    cfv
    wcel
    #
    @30
    @3
    @0
    @25
    @31
    @26
    @27
    @4
    cJ
    cX
    clsun.1
    clscld
    syl2anc
    @6
    cJ
    cX
    clsun.1
    cldss
    syl
    @6
    cX
    dfss4
    sylib
    @3
    @9
    cX
    wss
    #
    @10
    cX
    wss
    #
    wa
    #
    @13
    @11
    wceq
    #
    @3
    @32
    @33
    @0
    @1
    @32
    @2
    cA
    cJ
    cX
    clsun.1
    clsss3
    3adant3
    @0
    @2
    @33
    @1
    cB
    cJ
    cX
    clsun.1
    clsss3
    3adant2
    jca
    @34
    @11
    cX
    wss
    @35
    @9
    @10
    cX
    unss
    @11
    cX
    dfss4
    bitri
    sylib
    3eqtr3d
end
