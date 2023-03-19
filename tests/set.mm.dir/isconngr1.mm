include "cconngr.mm"
include "wcel.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cvtx.mm"
include "wsbc.mm"
include "cab.mm"
include "dfconngr1.mm"
include "eleq2i.mm"
include "fvex.mm"
include "wceq.mm"
include "id.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "sbcie.mm"
include "abbii.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "difeq1d.mm"
include "oveqd.mm"
include "breqd.mm"
include "2exbidv.mm"
include "weq.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "syl5bb.mm"

theorem isconngr1
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let cG: class G
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isconngr.v: |- V = ( Vtx ` G )

  disjoint f k
  disjoint f n
  disjoint f p
  disjoint k n
  disjoint k p
  disjoint n p
  disjoint G f
  disjoint G k
  disjoint G n
  disjoint G p
  disjoint V k
  disjoint V n
  disjoint f g
  disjoint f h
  disjoint f v
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g p
  disjoint g v
  disjoint h k
  disjoint h n
  disjoint h p
  disjoint h v
  disjoint k v
  disjoint n v
  disjoint p v
  disjoint G h
  disjoint V h
  assert |- ( G e. W -> ( G e. ConnGraph <-> A. k e. V A. n e. ( V \ { k } ) E. f E. p f ( k ( PathsOn ` G ) n ) p ) )

  proof
    cG
    cconngr
    wcel
    cG
    vf
    cv
    #
    vp
    cv
    #
    vk
    cv
    #
    vn
    cv
    #
    vg
    cv
    #
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    vv
    cv
    #
    @2
    csn
    #
    cdif
    #
    wral
    #
    vk
    @9
    wral
    #
    vv
    @4
    cvtx
    cfv
    #
    wsbc
    #
    vg
    cab
    #
    wcel
    #
    cG
    cW
    wcel
    #
    @0
    @1
    @2
    @3
    cG
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    cV
    @10
    cdif
    #
    wral
    #
    vk
    cV
    wral
    #
    cconngr
    @16
    cG
    vv
    vf
    vg
    vk
    vn
    vp
    dfconngr1
    eleq2i
    @17
    cG
    @8
    vn
    @14
    @10
    cdif
    #
    wral
    #
    vk
    @14
    wral
    #
    vg
    cab
    #
    wcel
    @18
    @25
    @16
    @29
    cG
    @15
    @28
    vg
    @13
    @28
    vv
    @14
    @4
    cvtx
    fvex
    @9
    @14
    wceq
    #
    @12
    @27
    vk
    @9
    @14
    @30
    id
    @30
    @8
    vn
    @11
    @26
    @9
    @14
    @10
    difeq1
    raleqdv
    raleqbidv
    sbcie
    abbii
    eleq2i
    @0
    @1
    @2
    @3
    vh
    cv
    #
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    vn
    @31
    cvtx
    cfv
    #
    @10
    cdif
    #
    wral
    #
    vk
    @36
    wral
    #
    @25
    vh
    cG
    @29
    cW
    @31
    cG
    wceq
    #
    @38
    @24
    vk
    @36
    cV
    @40
    @36
    cG
    cvtx
    cfv
    cV
    @31
    cG
    cvtx
    fveq2
    isconngr.v
    syl6eqr
    #
    @40
    @35
    @22
    vn
    @37
    @23
    @40
    @36
    cV
    @10
    @41
    difeq1d
    @40
    @34
    @21
    vf
    vp
    @40
    @33
    @20
    @0
    @1
    @40
    @32
    @19
    @2
    @3
    @31
    cG
    cpthson
    fveq2
    oveqd
    breqd
    2exbidv
    raleqbidv
    raleqbidv
    @28
    @39
    vg
    vh
    vg
    vh
    weq
    #
    @27
    @38
    vk
    @14
    @36
    @4
    @31
    cvtx
    fveq2
    #
    @42
    @8
    @35
    vn
    @26
    @37
    @42
    @14
    @36
    @10
    @43
    difeq1d
    @42
    @7
    @34
    vf
    vp
    @42
    @6
    @33
    @0
    @1
    @42
    @5
    @32
    @2
    @3
    @4
    @31
    cpthson
    fveq2
    oveqd
    breqd
    2exbidv
    raleqbidv
    raleqbidv
    cbvabv
    elab2g
    syl5bb
    syl5bb
end
