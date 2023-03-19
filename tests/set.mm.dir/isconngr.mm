include "cconngr.mm"
include "wcel.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wral.mm"
include "cvtx.mm"
include "wsbc.mm"
include "cab.mm"
include "df-conngr.mm"
include "eleq2i.mm"
include "fvex.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "sbcie.mm"
include "abbii.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "breqd.mm"
include "2exbidv.mm"
include "raleqbidv.mm"
include "weq.mm"
include "cbvabv.mm"
include "elab2g.mm"
include "syl5bb.mm"

theorem isconngr
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
  assert |- ( G e. W -> ( G e. ConnGraph <-> A. k e. V A. n e. V E. f E. p f ( k ( PathsOn ` G ) n ) p ) )

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
    wral
    #
    vk
    cV
    wral
    #
    cconngr
    @14
    cG
    vv
    vf
    vg
    vk
    vn
    vp
    df-conngr
    eleq2i
    @15
    cG
    @8
    vn
    @12
    wral
    #
    vk
    @12
    wral
    #
    vg
    cab
    #
    wcel
    @16
    @22
    @14
    @25
    cG
    @13
    @24
    vg
    @11
    @24
    vv
    @12
    @4
    cvtx
    fvex
    @10
    @23
    vk
    @9
    @12
    @8
    vn
    @9
    @12
    raleq
    raleqbi1dv
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
    @26
    cvtx
    cfv
    #
    wral
    #
    vk
    @31
    wral
    #
    @22
    vh
    cG
    @25
    cW
    @26
    cG
    wceq
    #
    @32
    @21
    vk
    @31
    cV
    @34
    @31
    cG
    cvtx
    cfv
    cV
    @26
    cG
    cvtx
    fveq2
    isconngr.v
    syl6eqr
    #
    @34
    @30
    @20
    vn
    @31
    cV
    @35
    @34
    @29
    @19
    vf
    vp
    @34
    @28
    @18
    @0
    @1
    @34
    @27
    @17
    @2
    @3
    @26
    cG
    cpthson
    fveq2
    oveqd
    breqd
    2exbidv
    raleqbidv
    raleqbidv
    @24
    @33
    vg
    vh
    vg
    vh
    weq
    #
    @23
    @32
    vk
    @12
    @31
    @4
    @26
    cvtx
    fveq2
    #
    @36
    @8
    @30
    vn
    @12
    @31
    @37
    @36
    @7
    @29
    vf
    vp
    @36
    @6
    @28
    @0
    @1
    @36
    @5
    @27
    @2
    @3
    @4
    @26
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
