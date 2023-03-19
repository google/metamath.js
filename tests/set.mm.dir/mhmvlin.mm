include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cmap.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cof.mm"
include "ccom.mm"
include "wa.mm"
include "wceq.mm"
include "simpl1.mm"
include "wf.mm"
include "elmapi.mm"
include "3ad2ant2.mm"
include "ffvelrnda.mm"
include "3ad2ant3.mm"
include "mhmlin.mm"
include "syl3anc.mm"
include "mpteq2dva.mm"
include "cmnd.mm"
include "mhmrcl1.mm"
include "adantr.mm"
include "3ad2antl1.mm"
include "mndcl.mm"
include "cvv.mm"
include "elmapex.mm"
include "simprd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "cbs.mm"
include "eqid.mm"
include "mhmf.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "fmptco.mm"
include "fvexd.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"

theorem mhmvlin
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume mhmvlin.b: |- B = ( Base ` M )
  assume mhmvlin.p: |- .+ = ( +g ` M )
  assume mhmvlin.q: |- .+^ = ( +g ` N )


  assert |- ( ( F e. ( M MndHom N ) /\ X e. ( B ^m I ) /\ Y e. ( B ^m I ) ) -> ( F o. ( X oF .+ Y ) ) = ( ( F o. X ) oF .+^ ( F o. Y ) ) )

  proof
    cF
    cM
    cN
    cmhm
    co
    wcel
    #
    cX
    cB
    cI
    cmap
    co
    #
    wcel
    #
    cY
    @1
    wcel
    #
    w3a
    #
    vy
    cI
    vy
    cv
    #
    cX
    cfv
    #
    @5
    cY
    cfv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    cmpt
    vy
    cI
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    c.pd
    co
    #
    cmpt
    cF
    cX
    cY
    c.pl
    cof
    co
    #
    ccom
    cF
    cX
    ccom
    #
    cF
    cY
    ccom
    #
    c.pd
    cof
    co
    @4
    vy
    cI
    @9
    @12
    @4
    @5
    cI
    wcel
    #
    wa
    #
    @0
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @9
    @12
    wceq
    @0
    @2
    @3
    @16
    simpl1
    @4
    cI
    cB
    @5
    cX
    @2
    @0
    cI
    cB
    cX
    wf
    #
    @3
    cX
    cB
    cI
    elmapi
    3ad2ant2
    #
    ffvelrnda
    #
    @4
    cI
    cB
    @5
    cY
    @3
    @0
    cI
    cB
    cY
    wf
    #
    @2
    cY
    cB
    cI
    elmapi
    3ad2ant3
    #
    ffvelrnda
    #
    cB
    c.pl
    c.pd
    cM
    cN
    cF
    @6
    @7
    mhmvlin.b
    mhmvlin.p
    mhmvlin.q
    mhmlin
    syl3anc
    mpteq2dva
    @4
    vy
    vz
    cI
    cB
    @8
    vz
    cv
    #
    cF
    cfv
    @9
    @13
    cF
    @17
    cM
    cmnd
    wcel
    #
    @18
    @19
    @8
    cB
    wcel
    @0
    @2
    @16
    @27
    @3
    @0
    @27
    @16
    cM
    cN
    cF
    mhmrcl1
    adantr
    3ad2antl1
    @22
    @25
    cB
    c.pl
    cM
    @6
    @7
    mhmvlin.b
    mhmvlin.p
    mndcl
    syl3anc
    @4
    vy
    cI
    @6
    @7
    c.pl
    cX
    cY
    cvv
    cB
    cB
    @3
    @0
    cI
    cvv
    wcel
    #
    @2
    @3
    cB
    cvv
    wcel
    @28
    cY
    cB
    cI
    elmapex
    simprd
    3ad2ant3
    #
    @22
    @25
    @4
    vy
    cI
    cB
    cX
    @21
    feqmptd
    @4
    vy
    cI
    cB
    cY
    @24
    feqmptd
    offval2
    @4
    vz
    cB
    cN
    cbs
    cfv
    #
    cF
    @0
    @2
    cB
    @30
    cF
    wf
    #
    @3
    cB
    @30
    cM
    cN
    cF
    mhmvlin.b
    @30
    eqid
    mhmf
    3ad2ant1
    #
    feqmptd
    @26
    @8
    cF
    fveq2
    fmptco
    @4
    vy
    cI
    @10
    @11
    c.pd
    @14
    @15
    cvv
    cvv
    cvv
    @29
    @17
    @6
    cF
    fvexd
    @17
    @7
    cF
    fvexd
    @4
    @31
    @20
    @14
    vy
    cI
    @10
    cmpt
    wceq
    @32
    @21
    vy
    cF
    cX
    cI
    cB
    @30
    fcompt
    syl2anc
    @4
    @31
    @23
    @15
    vy
    cI
    @11
    cmpt
    wceq
    @32
    @24
    vy
    cF
    cY
    cI
    cB
    @30
    fcompt
    syl2anc
    offval2
    3eqtr4d
end
