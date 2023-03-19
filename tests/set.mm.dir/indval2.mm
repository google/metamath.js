include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cind.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cxp.mm"
include "ciun.mm"
include "cdif.mm"
include "cun.mm"
include "cmpt.mm"
include "dfmpt3.mm"
include "indval.mm"
include "wceq.mm"
include "undif.mm"
include "biimpi.mm"
include "adantl.mm"
include "iuneq1d.mm"
include "3eqtr4a.mm"
include "iunxun.mm"
include "syl6eq.mm"
include "iftrue.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "iuneq2i.mm"
include "iunxpconst.mm"
include "eqtri.mm"
include "wn.mm"
include "eldifn.mm"
include "iffalse.mm"
include "syl.mm"
include "uneq12i.mm"

theorem indval2
  let cA: class A
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( ( O e. V /\ A C_ O ) -> ( ( _Ind ` O ) ` A ) = ( ( A X. { 1 } ) u. ( ( O \ A ) X. { 0 } ) ) )

  proof
    cO
    cV
    wcel
    #
    cA
    cO
    wss
    #
    wa
    #
    cA
    cO
    cind
    cfv
    cfv
    #
    vx
    cA
    vx
    cv
    #
    csn
    #
    @4
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    csn
    #
    cxp
    #
    ciun
    #
    vx
    cO
    cA
    cdif
    #
    @9
    ciun
    #
    cun
    #
    cA
    c1
    csn
    #
    cxp
    #
    @11
    cc0
    csn
    #
    cxp
    #
    cun
    @2
    @3
    vx
    cA
    @11
    cun
    #
    @9
    ciun
    #
    @13
    @2
    vx
    cO
    @7
    cmpt
    vx
    cO
    @9
    ciun
    @3
    @19
    vx
    cO
    @7
    dfmpt3
    vx
    cA
    cO
    cV
    indval
    @2
    vx
    @18
    cO
    @9
    @1
    @18
    cO
    wceq
    #
    @0
    @1
    @20
    cA
    cO
    undif
    biimpi
    adantl
    iuneq1d
    3eqtr4a
    vx
    cA
    @11
    @9
    iunxun
    syl6eq
    @10
    @15
    @12
    @17
    @10
    vx
    cA
    @5
    @14
    cxp
    #
    ciun
    @15
    vx
    cA
    @9
    @21
    @6
    @8
    @14
    @5
    @6
    @7
    c1
    @6
    c1
    cc0
    iftrue
    sneqd
    xpeq2d
    iuneq2i
    vx
    cA
    @14
    iunxpconst
    eqtri
    @12
    vx
    @11
    @5
    @16
    cxp
    #
    ciun
    @17
    vx
    @11
    @9
    @22
    @4
    @11
    wcel
    #
    @8
    @16
    @5
    @23
    @6
    wn
    #
    @8
    @16
    wceq
    @4
    cO
    cA
    eldifn
    @24
    @7
    cc0
    @6
    c1
    cc0
    iffalse
    sneqd
    syl
    xpeq2d
    iuneq2i
    vx
    @11
    @16
    iunxpconst
    eqtri
    uneq12i
    syl6eq
end
