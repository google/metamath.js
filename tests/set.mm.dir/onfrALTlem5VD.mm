include "cv.mm"
include "cin.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "inex1.mm"
include "sbcimg.mm"
include "e0a.mm"
include "sbcan.mm"
include "sseq1.mm"
include "sbcie.mm"
include "wn.mm"
include "df-ne.mm"
include "sbcbii.mm"
include "sbcng.mm"
include "bicomd.mm"
include "eqsbc3.mm"
include "necon3bbii.mm"
include "3bitr2i.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wex.mm"
include "df-rex.mm"
include "sbcel2gv.mm"
include "csb.mm"
include "sbceqg.mm"
include "csbin.mm"
include "csbvarg.mm"
include "csbconstg.mm"
include "ineq12i.mm"
include "eqtri.mm"
include "csb0.mm"
include "eqeq12i.mm"
include "exbii.mm"
include "sbcex2.mm"
include "3bitr4i.mm"
include "imbi12i.mm"

theorem onfrALTlem5VD
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b

  disjoint a b
  disjoint a y
  disjoint b y
  disjoint b x
  disjoint x y
  assert |- ( [. ( a i^i x ) / b ]. ( ( b C_ ( a i^i x ) /\ b =/= (/) ) -> E. y e. b ( b i^i y ) = (/) ) <-> ( ( ( a i^i x ) C_ ( a i^i x ) /\ ( a i^i x ) =/= (/) ) -> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) )

  proof
    vb
    cv
    #
    va
    cv
    #
    vx
    cv
    #
    cin
    #
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    @0
    vy
    cv
    #
    cin
    #
    c0
    wceq
    #
    vy
    @0
    wrex
    #
    wi
    vb
    @3
    wsbc
    #
    @6
    vb
    @3
    wsbc
    #
    @10
    vb
    @3
    wsbc
    #
    wi
    #
    @3
    @3
    wss
    #
    @3
    c0
    wne
    #
    wa
    #
    @3
    @7
    cin
    #
    c0
    wceq
    #
    vy
    @3
    wrex
    #
    wi
    @3
    cvv
    wcel
    #
    @11
    @14
    wb
    @1
    @2
    va
    vex
    inex1
    #
    @6
    @10
    vb
    @3
    cvv
    sbcimg
    e0a
    @12
    @17
    @13
    @20
    @12
    @4
    vb
    @3
    wsbc
    #
    @5
    vb
    @3
    wsbc
    #
    wa
    @17
    @4
    @5
    vb
    @3
    sbcan
    @23
    @15
    @24
    @16
    @4
    @15
    vb
    @3
    @22
    @0
    @3
    @3
    sseq1
    sbcie
    @24
    @0
    c0
    wceq
    #
    wn
    #
    vb
    @3
    wsbc
    #
    @25
    vb
    @3
    wsbc
    #
    wn
    #
    @16
    @5
    @26
    vb
    @3
    @0
    c0
    df-ne
    sbcbii
    @21
    @29
    @27
    wb
    @22
    @21
    @27
    @29
    @25
    vb
    @3
    cvv
    sbcng
    bicomd
    e0a
    @28
    @3
    c0
    @21
    @28
    @3
    c0
    wceq
    wb
    @22
    vb
    @3
    c0
    cvv
    eqsbc3
    e0a
    necon3bbii
    3bitr2i
    anbi12i
    bitri
    @13
    @7
    @0
    wcel
    #
    @9
    wa
    #
    vy
    wex
    #
    vb
    @3
    wsbc
    #
    @20
    @10
    @32
    vb
    @3
    @9
    vy
    @0
    df-rex
    sbcbii
    @31
    vb
    @3
    wsbc
    #
    vy
    wex
    @7
    @3
    wcel
    #
    @19
    wa
    #
    vy
    wex
    @33
    @20
    @34
    @36
    vy
    @34
    @30
    vb
    @3
    wsbc
    #
    @9
    vb
    @3
    wsbc
    #
    wa
    @36
    @30
    @9
    vb
    @3
    sbcan
    @37
    @35
    @38
    @19
    @21
    @37
    @35
    wb
    @22
    vb
    @7
    @3
    cvv
    sbcel2gv
    e0a
    @38
    vb
    @3
    @8
    csb
    #
    vb
    @3
    c0
    csb
    #
    wceq
    #
    @19
    @21
    @38
    @41
    wb
    @22
    vb
    @3
    @8
    c0
    cvv
    sbceqg
    e0a
    @39
    @18
    @40
    c0
    @39
    vb
    @3
    @0
    csb
    #
    vb
    @3
    @7
    csb
    #
    cin
    @18
    vb
    @3
    @0
    @7
    csbin
    @42
    @3
    @43
    @7
    @21
    @42
    @3
    wceq
    @22
    vb
    @3
    cvv
    csbvarg
    e0a
    @21
    @43
    @7
    wceq
    @22
    vb
    @3
    @7
    cvv
    csbconstg
    e0a
    ineq12i
    eqtri
    vb
    @3
    csb0
    eqeq12i
    bitri
    anbi12i
    bitri
    exbii
    @31
    vy
    vb
    @3
    sbcex2
    @19
    vy
    @3
    df-rex
    3bitr4i
    bitri
    imbi12i
    bitri
end
