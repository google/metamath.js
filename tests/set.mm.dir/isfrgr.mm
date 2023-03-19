include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cusgr.mm"
include "cpr.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cedg.mm"
include "cfv.mm"
include "wsbc.mm"
include "cvtx.mm"
include "wa.mm"
include "cab.mm"
include "df-frgr.mm"
include "eleq2i.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "wb.mm"
include "reueq1.mm"
include "syl.mm"
include "sseq2d.mm"
include "reubidv.mm"
include "bitrd.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "weq.mm"
include "cvv.mm"
include "fvexd.mm"
include "adantr.mm"
include "simpr.mm"
include "difeq1.mm"
include "ad2antlr.mm"
include "sbcied2.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "syl5bb.mm"

theorem isfrgr
  let vx: setvar x
  let cU: class U
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cV: class V
  let vl: setvar l
  let ve: setvar e
  let vh: setvar h
  let vg: setvar g
  let vv: setvar v
  assume isfrgr.v: |- V = ( Vtx ` G )
  assume isfrgr.e: |- E = ( Edg ` G )

  disjoint k l
  disjoint k x
  disjoint l x
  disjoint G k
  disjoint G l
  disjoint G x
  disjoint V k
  disjoint V l
  disjoint V x
  disjoint e h
  disjoint g h
  disjoint h k
  disjoint h l
  disjoint h x
  disjoint h v
  disjoint e g
  disjoint e k
  disjoint e l
  disjoint e x
  disjoint e v
  disjoint g k
  disjoint g l
  disjoint g x
  disjoint g v
  disjoint k v
  disjoint l v
  disjoint v x
  disjoint E h
  disjoint G h
  disjoint V h
  assert |- ( G e. U -> ( G e. FriendGraph <-> ( G e. USGraph /\ A. k e. V A. l e. ( V \ { k } ) E! x e. V { { x , k } , { x , l } } C_ E ) ) )

  proof
    cG
    cfrgr
    wcel
    cG
    vg
    cv
    #
    cusgr
    wcel
    #
    vx
    cv
    #
    vk
    cv
    #
    cpr
    @2
    vl
    cv
    cpr
    cpr
    #
    ve
    cv
    #
    wss
    #
    vx
    vv
    cv
    #
    wreu
    #
    vl
    @7
    @3
    csn
    #
    cdif
    #
    wral
    #
    vk
    @7
    wral
    #
    ve
    @0
    cedg
    cfv
    #
    wsbc
    #
    vv
    @0
    cvtx
    cfv
    #
    wsbc
    #
    wa
    #
    vg
    cab
    #
    wcel
    cG
    cU
    wcel
    cG
    cusgr
    wcel
    #
    @4
    cE
    wss
    #
    vx
    cV
    wreu
    #
    vl
    cV
    @9
    cdif
    #
    wral
    #
    vk
    cV
    wral
    #
    wa
    #
    cfrgr
    @18
    cG
    vx
    vv
    ve
    vg
    vk
    vl
    df-frgr
    eleq2i
    vh
    cv
    #
    cusgr
    wcel
    #
    @4
    @26
    cedg
    cfv
    #
    wss
    #
    vx
    @26
    cvtx
    cfv
    #
    wreu
    #
    vl
    @30
    @9
    cdif
    #
    wral
    #
    vk
    @30
    wral
    #
    wa
    #
    @25
    vh
    cG
    @18
    cU
    @26
    cG
    wceq
    #
    @27
    @19
    @34
    @24
    @26
    cG
    cusgr
    eleq1
    @36
    @33
    @23
    vk
    @30
    cV
    @36
    @30
    cG
    cvtx
    cfv
    cV
    @26
    cG
    cvtx
    fveq2
    isfrgr.v
    syl6eqr
    #
    @36
    @31
    @21
    vl
    @32
    @22
    @36
    @30
    cV
    @9
    @37
    difeq1d
    @36
    @31
    @29
    vx
    cV
    wreu
    #
    @21
    @36
    @30
    cV
    wceq
    @31
    @38
    wb
    @37
    @29
    vx
    @30
    cV
    reueq1
    syl
    @36
    @29
    @20
    vx
    cV
    @36
    @28
    cE
    @4
    @36
    @28
    cG
    cedg
    cfv
    cE
    @26
    cG
    cedg
    fveq2
    isfrgr.e
    syl6eqr
    sseq2d
    reubidv
    bitrd
    raleqbidv
    raleqbidv
    anbi12d
    @17
    @35
    vg
    vh
    vg
    vh
    weq
    #
    @1
    @27
    @16
    @34
    @0
    @26
    cusgr
    eleq1
    @39
    @14
    @34
    vv
    @15
    @30
    cvv
    @39
    @0
    cvtx
    fvexd
    @0
    @26
    cvtx
    fveq2
    @39
    @7
    @30
    wceq
    #
    wa
    #
    @12
    @34
    ve
    @13
    @28
    cvv
    @41
    @0
    cedg
    fvexd
    @39
    @13
    @28
    wceq
    @40
    @0
    @26
    cedg
    fveq2
    adantr
    @41
    @5
    @28
    wceq
    #
    wa
    #
    @11
    @33
    vk
    @7
    @30
    @41
    @40
    @42
    @39
    @40
    simpr
    adantr
    @43
    @8
    @31
    vl
    @10
    @32
    @40
    @10
    @32
    wceq
    @39
    @42
    @7
    @30
    @9
    difeq1
    ad2antlr
    @43
    @8
    @6
    vx
    @30
    wreu
    #
    @31
    @40
    @8
    @44
    wb
    @39
    @42
    @6
    vx
    @7
    @30
    reueq1
    ad2antlr
    @43
    @6
    @29
    vx
    @30
    @43
    @5
    @28
    @4
    @41
    @42
    simpr
    sseq2d
    reubidv
    bitrd
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    anbi12d
    cbvabv
    elab2g
    syl5bb
end
