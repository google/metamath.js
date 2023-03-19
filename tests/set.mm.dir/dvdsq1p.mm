include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "uc1pcl.mm"
include "3ad2ant3.mm"
include "dvdsr2.mm"
include "syl.mm"
include "wa.mm"
include "eqcom.mm"
include "simprr.mm"
include "csg.mm"
include "cfv.mm"
include "cdg1.mm"
include "clt.mm"
include "simprl.mm"
include "cmnf.mm"
include "c0g.mm"
include "cgrp.mm"
include "simpl1.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "simpl2.mm"
include "simpr.mm"
include "adantr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "grpsubeq0.mm"
include "biimprd.mm"
include "impr.mm"
include "fveq2d.mm"
include "deg1z.mm"
include "eqtrd.mm"
include "cr.mm"
include "cn0.mm"
include "uc1pdeg.mm"
include "3adant2.mm"
include "nn0red.mm"
include "mnflt.mm"
include "eqbrtrd.mm"
include "q1peqb.mm"
include "mpbi2and.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "expr.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "q1pcl.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem dvdsq1p
  let cB: class B
  let cC: class C
  let c.pa: class .||
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let vq: setvar q
  assume dvdsq1p.p: |- P = ( Poly1 ` R )
  assume dvdsq1p.d: |- .|| = ( ||r ` P )
  assume dvdsq1p.b: |- B = ( Base ` P )
  assume dvdsq1p.c: |- C = ( Unic1p ` R )
  assume dvdsq1p.t: |- .x. = ( .r ` P )
  assume dvdsq1p.q: |- Q = ( quot1p ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( G .|| F <-> F = ( ( F Q G ) .x. G ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cC
    wcel
    #
    w3a
    #
    cG
    cF
    c.pa
    wbr
    #
    cF
    cF
    cG
    cQ
    co
    #
    cG
    c.x
    co
    #
    wceq
    #
    @3
    @4
    vq
    cv
    #
    cG
    c.x
    co
    #
    cF
    wceq
    #
    vq
    cB
    wrex
    #
    @7
    @3
    cG
    cB
    wcel
    #
    @4
    @11
    wb
    @2
    @0
    @12
    @1
    cB
    cC
    cP
    cR
    cG
    dvdsq1p.p
    dvdsq1p.b
    dvdsq1p.c
    uc1pcl
    3ad2ant3
    #
    vq
    cB
    c.pa
    cP
    c.x
    cG
    cF
    dvdsq1p.b
    dvdsq1p.d
    dvdsq1p.t
    dvdsr2
    syl
    @3
    @10
    @7
    vq
    cB
    @10
    cF
    @9
    wceq
    #
    @3
    @8
    cB
    wcel
    #
    wa
    #
    @7
    @9
    cF
    eqcom
    @3
    @15
    @14
    @7
    @3
    @15
    @14
    wa
    #
    wa
    #
    cF
    @9
    @6
    @3
    @15
    @14
    simprr
    @18
    @5
    @8
    cG
    c.x
    @18
    @15
    cF
    @9
    cP
    csg
    cfv
    #
    co
    #
    cR
    cdg1
    cfv
    #
    cfv
    #
    cG
    @21
    cfv
    #
    clt
    wbr
    #
    @5
    @8
    wceq
    #
    @3
    @15
    @14
    simprl
    @18
    @22
    cmnf
    @23
    clt
    @18
    @22
    cP
    c0g
    cfv
    #
    @21
    cfv
    #
    cmnf
    @18
    @20
    @26
    @21
    @3
    @15
    @14
    @20
    @26
    wceq
    #
    @16
    @28
    @14
    @16
    cP
    cgrp
    wcel
    #
    @1
    @9
    cB
    wcel
    #
    @28
    @14
    wb
    @16
    cP
    crg
    wcel
    #
    @29
    @16
    @0
    @31
    @0
    @1
    @2
    @15
    simpl1
    cP
    cR
    dvdsq1p.p
    ply1ring
    syl
    #
    cP
    ringgrp
    syl
    @0
    @1
    @2
    @15
    simpl2
    @16
    @31
    @15
    @12
    @30
    @32
    @3
    @15
    simpr
    @3
    @12
    @15
    @13
    adantr
    cB
    cP
    c.x
    @8
    cG
    dvdsq1p.b
    dvdsq1p.t
    ringcl
    syl3anc
    cB
    cP
    @19
    cF
    @9
    @26
    dvdsq1p.b
    @26
    eqid
    #
    @19
    eqid
    #
    grpsubeq0
    syl3anc
    biimprd
    impr
    fveq2d
    @18
    @0
    @27
    cmnf
    wceq
    @0
    @1
    @2
    @17
    simpl1
    @21
    cP
    cR
    @26
    @21
    eqid
    #
    dvdsq1p.p
    @33
    deg1z
    syl
    eqtrd
    @18
    @23
    cr
    wcel
    #
    cmnf
    @23
    clt
    wbr
    @3
    @36
    @17
    @3
    @23
    @0
    @2
    @23
    cn0
    wcel
    @1
    cC
    @21
    cR
    cG
    @35
    dvdsq1p.c
    uc1pdeg
    3adant2
    nn0red
    adantr
    @23
    mnflt
    syl
    eqbrtrd
    @3
    @15
    @24
    wa
    @25
    wb
    @17
    cB
    cC
    @21
    cP
    cQ
    cR
    c.x
    cF
    cG
    @19
    @8
    dvdsq1p.q
    dvdsq1p.p
    dvdsq1p.b
    @35
    @34
    dvdsq1p.t
    dvdsq1p.c
    q1peqb
    adantr
    mpbi2and
    oveq1d
    eqtr4d
    expr
    syl5bi
    rexlimdva
    sylbid
    @3
    @4
    @7
    cG
    @6
    c.pa
    wbr
    #
    @3
    @12
    @5
    cB
    wcel
    @37
    @13
    cB
    cC
    cP
    cQ
    cR
    cF
    cG
    dvdsq1p.q
    dvdsq1p.p
    dvdsq1p.b
    dvdsq1p.c
    q1pcl
    cB
    c.pa
    cP
    c.x
    cG
    @5
    dvdsq1p.b
    dvdsq1p.d
    dvdsq1p.t
    dvdsrmul
    syl2anc
    cF
    @6
    cG
    c.pa
    breq2
    syl5ibrcom
    impbid
end
