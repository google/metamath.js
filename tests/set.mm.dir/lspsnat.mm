include "clvec.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "simprl.mm"
include "clmod.mm"
include "simpl1.mm"
include "lveclmod.mm"
include "syl.mm"
include "simpl2.mm"
include "simprr.mm"
include "eldifad.mm"
include "lspsnel5a.mm"
include "cun.mm"
include "0ss.mm"
include "a1i.mm"
include "simpl3.mm"
include "ssdif.mm"
include "ad2antrl.mm"
include "sseldd.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "lsp0.mm"
include "difeq12d.mm"
include "eleqtrrd.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "syl6eleq.mm"
include "eqssd.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "necon1bd.mm"
include "ssdif0.mm"
include "syl6ibr.mm"
include "wb.mm"
include "lssle0.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "orrd.mm"

theorem lspsnat
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume lspsnat.v: |- V = ( Base ` W )
  assume lspsnat.z: |- .0. = ( 0g ` W )
  assume lspsnat.s: |- S = ( LSubSp ` W )
  assume lspsnat.n: |- N = ( LSpan ` W )


  assert |- ( ( ( W e. LVec /\ U e. S /\ X e. V ) /\ U C_ ( N ` { X } ) ) -> ( U = ( N ` { X } ) \/ U = { .0. } ) )

  proof
    cW
    clvec
    wcel
    #
    cU
    cS
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cU
    cX
    csn
    #
    cN
    cfv
    #
    wss
    #
    wa
    #
    cU
    @5
    wceq
    #
    cU
    c.0
    csn
    #
    wceq
    #
    @7
    @8
    wn
    #
    cU
    @9
    wss
    #
    @10
    @7
    @11
    cU
    @9
    cdif
    #
    c0
    wceq
    @12
    @7
    @8
    @13
    c0
    @13
    c0
    wne
    vx
    cv
    #
    @13
    wcel
    #
    vx
    wex
    @7
    @8
    vx
    @13
    n0
    @7
    @15
    @8
    vx
    @3
    @6
    @15
    @8
    @3
    @6
    @15
    wa
    #
    wa
    #
    cU
    @5
    @3
    @6
    @15
    simprl
    @17
    cS
    cU
    cN
    cW
    cX
    lspsnat.s
    lspsnat.n
    @17
    @0
    cW
    clmod
    wcel
    #
    @0
    @1
    @2
    @16
    simpl1
    #
    cW
    lveclmod
    #
    syl
    #
    @0
    @1
    @2
    @16
    simpl2
    #
    @17
    @14
    csn
    #
    cN
    cfv
    #
    cU
    cX
    @17
    cS
    cU
    cN
    cW
    @14
    lspsnat.s
    lspsnat.n
    @21
    @22
    @17
    @14
    cU
    @9
    @3
    @6
    @15
    simprr
    #
    eldifad
    lspsnel5a
    @17
    cX
    c0
    @23
    cun
    #
    cN
    cfv
    #
    @24
    @17
    @0
    c0
    cV
    wss
    #
    @2
    @14
    c0
    @4
    cun
    #
    cN
    cfv
    #
    c0
    cN
    cfv
    #
    cdif
    #
    wcel
    cX
    @27
    wcel
    @19
    @28
    @17
    cV
    0ss
    a1i
    @0
    @1
    @2
    @16
    simpl3
    @17
    @14
    @5
    @9
    cdif
    #
    @32
    @17
    @13
    @33
    @14
    @6
    @13
    @33
    wss
    @3
    @15
    cU
    @5
    @9
    ssdif
    ad2antrl
    @25
    sseldd
    @17
    @30
    @5
    @31
    @9
    @30
    @5
    wceq
    @17
    @29
    @4
    cN
    @29
    @4
    c0
    cun
    @4
    c0
    @4
    uncom
    @4
    un0
    eqtri
    fveq2i
    a1i
    @17
    @18
    @31
    @9
    wceq
    @21
    cN
    cW
    c.0
    lspsnat.z
    lspsnat.n
    lsp0
    syl
    difeq12d
    eleqtrrd
    c0
    cS
    cN
    cV
    cW
    @14
    cX
    lspsnat.v
    lspsnat.s
    lspsnat.n
    lspsolv
    syl13anc
    @26
    @23
    cN
    @26
    @23
    c0
    cun
    @23
    c0
    @23
    uncom
    @23
    un0
    eqtri
    fveq2i
    syl6eleq
    sseldd
    lspsnel5a
    eqssd
    expr
    exlimdv
    syl5bi
    necon1bd
    cU
    @9
    ssdif0
    syl6ibr
    @7
    @18
    @1
    @12
    @10
    wb
    @7
    @0
    @18
    @0
    @1
    @2
    @6
    simpl1
    @20
    syl
    @0
    @1
    @2
    @6
    simpl2
    cS
    cW
    cU
    c.0
    lspsnat.z
    lspsnat.s
    lssle0
    syl2anc
    sylibd
    orrd
end
