include "wcel.mm"
include "cip.mm"
include "cfv.mm"
include "crefld.mm"
include "cr.mm"
include "csra.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cress.mm"
include "ctch.mm"
include "cmap.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "rrxprds.mm"
include "fveq2d.mm"
include "eqid.mm"
include "tchip.mm"
include "cvv.mm"
include "wceq.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ressip.mm"
include "ax-mp.mm"
include "cfield.mm"
include "refld.mm"
include "a1i.mm"
include "snex.mm"
include "xpexg.mm"
include "mpan2.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "snnz.mm"
include "dmxp.mm"
include "prdsip.mm"
include "cixp.mm"
include "prdsbas.mm"
include "eqidd.mm"
include "wss.mm"
include "rebase.mm"
include "eqimssi.mm"
include "srabase.mm"
include "fvconst2.mm"
include "3eqtr4rd.mm"
include "adantl.mm"
include "ixpeq2dva.mm"
include "reex.mm"
include "ixpconstg.mm"
include "3eqtrd.mm"
include "cmulr.mm"
include "remulr.mm"
include "sraip.mm"
include "syl5req.mm"
include "oveqd.mm"
include "mpteq2ia.mm"
include "oveq2d.mm"
include "mpt2eq123dv.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"

theorem rrxip
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cV: class V
  let vh: setvar h
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )
  assume rrxbase.b: |- B = ( Base ` H )

  disjoint f g
  disjoint f x
  disjoint B f
  disjoint g x
  disjoint B g
  disjoint B x
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint f h
  disjoint g h
  disjoint h x
  disjoint B h
  disjoint f i
  disjoint g i
  disjoint h i
  disjoint I h
  disjoint i x
  disjoint I i
  disjoint V h
  assert |- ( I e. V -> ( f e. ( RR ^m I ) , g e. ( RR ^m I ) |-> ( RRfld gsum ( x e. I |-> ( ( f ` x ) x. ( g ` x ) ) ) ) ) = ( .i ` H ) )

  proof
    cI
    cV
    wcel
    #
    cH
    cip
    cfv
    crefld
    cI
    cr
    crefld
    csra
    cfv
    #
    cfv
    #
    csn
    #
    cxp
    #
    cprds
    co
    #
    cB
    cress
    co
    #
    ctch
    cfv
    #
    cip
    cfv
    #
    vf
    vg
    cr
    cI
    cmap
    co
    #
    @9
    crefld
    vx
    cI
    vx
    cv
    #
    vf
    cv
    cfv
    #
    @10
    vg
    cv
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    @0
    cH
    @7
    cip
    cB
    cH
    cI
    cV
    rrxval.r
    rrxbase.b
    rrxprds
    fveq2d
    @0
    @8
    @6
    cip
    cfv
    #
    @16
    @17
    @7
    @6
    @7
    eqid
    @17
    eqid
    tchip
    @0
    @17
    @5
    cip
    cfv
    #
    @16
    cB
    cvv
    wcel
    @18
    @17
    wceq
    cB
    cH
    cbs
    cfv
    cvv
    rrxbase.b
    cH
    cbs
    fvex
    eqeltri
    cB
    @5
    @6
    @18
    cvv
    @6
    eqid
    @18
    eqid
    #
    ressip
    ax-mp
    @0
    @18
    vf
    vg
    @5
    cbs
    cfv
    #
    @20
    crefld
    vx
    cI
    @11
    @12
    @10
    @4
    cfv
    #
    cip
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    @16
    @0
    vx
    @20
    @5
    @4
    crefld
    vf
    vg
    @18
    cI
    cfield
    cvv
    @5
    eqid
    #
    crefld
    cfield
    wcel
    @0
    refld
    a1i
    #
    @0
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @2
    snex
    cI
    @3
    cV
    cvv
    xpexg
    mpan2
    #
    @20
    eqid
    #
    @4
    cdm
    cI
    wceq
    #
    @0
    @3
    c0
    wne
    @30
    @2
    cr
    @1
    fvex
    #
    snnz
    cI
    @3
    dmxp
    ax-mp
    a1i
    #
    @19
    prdsip
    @0
    vf
    vg
    @20
    @20
    @25
    @9
    @9
    @15
    @0
    @20
    vx
    cI
    @21
    cbs
    cfv
    #
    cixp
    vx
    cI
    cr
    cixp
    #
    @9
    @0
    vx
    @20
    @5
    @4
    crefld
    cI
    cfield
    cvv
    @26
    @27
    @28
    @29
    @32
    prdsbas
    @0
    vx
    cI
    @33
    cr
    @10
    cI
    wcel
    #
    @33
    cr
    wceq
    @0
    @35
    crefld
    cbs
    cfv
    #
    @2
    cbs
    cfv
    cr
    @33
    @35
    @2
    cr
    crefld
    @35
    @2
    eqidd
    cr
    @36
    wss
    @35
    cr
    @36
    rebase
    eqimssi
    a1i
    #
    srabase
    cr
    @36
    wceq
    @35
    rebase
    a1i
    @35
    @21
    @2
    cbs
    cI
    @2
    @10
    @31
    fvconst2
    #
    fveq2d
    3eqtr4rd
    adantl
    ixpeq2dva
    @0
    cr
    cvv
    wcel
    @34
    @9
    wceq
    reex
    vx
    cI
    cr
    cV
    cvv
    ixpconstg
    mpan2
    3eqtrd
    #
    @39
    @0
    @24
    @14
    crefld
    cgsu
    @24
    @14
    wceq
    @0
    vx
    cI
    @23
    @13
    @35
    @22
    cmul
    @11
    @12
    @35
    cmul
    crefld
    cmulr
    cfv
    @22
    remulr
    @35
    @21
    cr
    crefld
    @38
    @37
    sraip
    syl5req
    oveqd
    mpteq2ia
    a1i
    oveq2d
    mpt2eq123dv
    eqtrd
    syl5eqr
    syl5eqr
    eqtr2d
end
