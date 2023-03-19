include "wcel.mm"
include "wa.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmap.mm"
include "cmpt2.mm"
include "wf.mm"
include "wfn.mm"
include "frlmbasmap.mm"
include "ad2ant2r.mm"
include "elmapi.mm"
include "ffn.mm"
include "3syl.mm"
include "ad2ant2rl.mm"
include "simpll.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "oveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "ovexd.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "ovmpt2g.mm"
include "syl3anc.mm"
include "cip.mm"
include "frlmip.mm"
include "adantr.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "3eqtr2rd.mm"

theorem frlmipval
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let c.xi: class .,
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume frlmphl.y: |- Y = ( R freeLMod I )
  assume frlmphl.b: |- B = ( Base ` R )
  assume frlmphl.t: |- .x. = ( .r ` R )
  assume frlmphl.v: |- V = ( Base ` Y )
  assume frlmphl.j: |- ., = ( .i ` Y )


  assert |- ( ( ( I e. W /\ R e. X ) /\ ( F e. V /\ G e. V ) ) -> ( F ., G ) = ( R gsum ( F oF .x. G ) ) )

  proof
    cI
    cW
    wcel
    #
    cR
    cX
    wcel
    #
    wa
    #
    cF
    cV
    wcel
    #
    cG
    cV
    wcel
    #
    wa
    #
    wa
    #
    cR
    cF
    cG
    c.x
    cof
    co
    #
    cgsu
    co
    cR
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @8
    cG
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cF
    cG
    vf
    vg
    cB
    cI
    cmap
    co
    #
    @14
    cR
    vx
    cI
    @8
    vf
    cv
    #
    cfv
    #
    @8
    vg
    cv
    #
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    co
    #
    cF
    cG
    c.xi
    co
    @6
    @7
    @12
    cR
    cgsu
    @6
    vx
    cI
    cI
    @9
    @10
    c.x
    cI
    cF
    cG
    cW
    cW
    @6
    cF
    @14
    wcel
    #
    cI
    cB
    cF
    wf
    cF
    cI
    wfn
    @0
    @3
    @24
    @1
    @4
    cV
    cR
    cY
    cI
    cB
    cW
    cF
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    ad2ant2r
    #
    cF
    cB
    cI
    elmapi
    cI
    cB
    cF
    ffn
    3syl
    @6
    cG
    @14
    wcel
    #
    cI
    cB
    cG
    wf
    cG
    cI
    wfn
    @0
    @4
    @26
    @1
    @3
    cV
    cR
    cY
    cI
    cB
    cW
    cG
    frlmphl.y
    frlmphl.b
    frlmphl.v
    frlmbasmap
    ad2ant2rl
    #
    cG
    cB
    cI
    elmapi
    cI
    cB
    cG
    ffn
    3syl
    @0
    @1
    @5
    simpll
    #
    @28
    cI
    inidm
    @6
    @8
    cI
    wcel
    wa
    #
    @9
    eqidd
    @29
    @10
    eqidd
    offval
    oveq2d
    @6
    @24
    @26
    @13
    cvv
    wcel
    @23
    @13
    wceq
    @25
    @27
    @6
    cR
    @12
    cgsu
    ovexd
    vf
    vg
    cF
    cG
    @14
    @14
    @21
    @13
    @22
    cR
    vx
    cI
    @9
    @18
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cvv
    @15
    cF
    wceq
    #
    @20
    @31
    cR
    cgsu
    @32
    vx
    cI
    @19
    @30
    @32
    @16
    @9
    @18
    c.x
    @8
    @15
    cF
    fveq1
    oveq1d
    mpteq2dv
    oveq2d
    @17
    cG
    wceq
    #
    @31
    @12
    cR
    cgsu
    @33
    vx
    cI
    @30
    @11
    @33
    @18
    @10
    @9
    c.x
    @8
    @17
    cG
    fveq1
    oveq2d
    mpteq2dv
    oveq2d
    @22
    eqid
    ovmpt2g
    syl3anc
    @6
    @22
    c.xi
    cF
    cG
    @6
    @22
    cY
    cip
    cfv
    #
    c.xi
    @2
    @22
    @34
    wceq
    @5
    vx
    cB
    cR
    c.x
    vf
    vg
    cI
    cX
    cW
    cY
    frlmphl.y
    frlmphl.b
    frlmphl.t
    frlmip
    adantr
    frlmphl.j
    syl6eqr
    oveqd
    3eqtr2rd
end
