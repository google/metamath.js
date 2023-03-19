include "cgrp.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "simpl.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "c0g.mm"
include "cmg.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "grpass.mm"
include "syl13anc.mm"
include "mulg2.mm"
include "syl.mm"
include "simp1r.mm"
include "gexdvdsi.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "grprid.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "grpcl.mm"
include "wb.mm"
include "grplcan.mm"
include "mpbid.mm"
include "isabld.mm"

theorem gex2abl
  let cE: class E
  let cG: class G
  let cX: class X
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let cO: class O
  let wph: wff ph
  assume gexex.1: |- X = ( Base ` G )
  assume gexex.2: |- E = ( gEx ` G )


  assert |- ( ( G e. Grp /\ E || 2 ) -> G e. Abel )

  proof
    cG
    cgrp
    wcel
    #
    cE
    c2
    cdvds
    wbr
    #
    wa
    #
    vx
    vy
    cX
    cG
    cplusg
    cfv
    #
    cG
    cX
    cG
    cbs
    cfv
    wceq
    @2
    gexex.1
    a1i
    @2
    @3
    eqidd
    @0
    @1
    simpl
    @2
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    w3a
    #
    @4
    @6
    @3
    co
    #
    @9
    @3
    co
    #
    @9
    @6
    @4
    @3
    co
    #
    @3
    co
    #
    wceq
    #
    @9
    @11
    wceq
    #
    @8
    @9
    @6
    @3
    co
    #
    @4
    @3
    co
    #
    @10
    @12
    @8
    @16
    cG
    c0g
    cfv
    #
    c2
    @9
    cG
    cmg
    cfv
    #
    co
    #
    @10
    @8
    @16
    @4
    @4
    @3
    co
    #
    c2
    @4
    @18
    co
    #
    @17
    @8
    @15
    @4
    @4
    @3
    @8
    @15
    @4
    @6
    @6
    @3
    co
    #
    @3
    co
    #
    @4
    @17
    @3
    co
    #
    @4
    @8
    @0
    @5
    @7
    @7
    @15
    @23
    wceq
    @0
    @1
    @5
    @7
    simp1l
    #
    @2
    @5
    @7
    simp2
    #
    @2
    @5
    @7
    simp3
    #
    @27
    cX
    @3
    cG
    @4
    @6
    @6
    gexex.1
    @3
    eqid
    #
    grpass
    syl13anc
    @8
    @22
    @17
    @4
    @3
    @8
    c2
    @6
    @18
    co
    #
    @22
    @17
    @8
    @7
    @29
    @22
    wceq
    @27
    cX
    @3
    @18
    cG
    @6
    gexex.1
    @18
    eqid
    #
    @28
    mulg2
    syl
    @8
    @0
    @7
    @1
    @29
    @17
    wceq
    @25
    @27
    @0
    @1
    @5
    @7
    simp1r
    #
    @6
    @18
    cE
    cG
    c2
    cX
    @17
    gexex.1
    gexex.2
    @30
    @17
    eqid
    #
    gexdvdsi
    syl3anc
    eqtr3d
    oveq2d
    @8
    @0
    @5
    @24
    @4
    wceq
    @25
    @26
    cX
    @3
    cG
    @4
    @17
    gexex.1
    @28
    @32
    grprid
    syl2anc
    3eqtrd
    oveq1d
    @8
    @5
    @21
    @20
    wceq
    @26
    cX
    @3
    @18
    cG
    @4
    gexex.1
    @30
    @28
    mulg2
    syl
    @8
    @0
    @5
    @1
    @21
    @17
    wceq
    @25
    @26
    @31
    @4
    @18
    cE
    cG
    c2
    cX
    @17
    gexex.1
    gexex.2
    @30
    @32
    gexdvdsi
    syl3anc
    3eqtr2d
    @8
    @0
    @9
    cX
    wcel
    #
    @1
    @19
    @17
    wceq
    @25
    @8
    @0
    @5
    @7
    @33
    @25
    @26
    @27
    cX
    @3
    cG
    @4
    @6
    gexex.1
    @28
    grpcl
    syl3anc
    #
    @31
    @9
    @18
    cE
    cG
    c2
    cX
    @17
    gexex.1
    gexex.2
    @30
    @32
    gexdvdsi
    syl3anc
    @8
    @33
    @19
    @10
    wceq
    @34
    cX
    @3
    @18
    cG
    @9
    gexex.1
    @30
    @28
    mulg2
    syl
    3eqtr2d
    @8
    @0
    @33
    @7
    @5
    @16
    @12
    wceq
    @25
    @34
    @27
    @26
    cX
    @3
    cG
    @9
    @6
    @4
    gexex.1
    @28
    grpass
    syl13anc
    eqtr3d
    @8
    @0
    @33
    @11
    cX
    wcel
    #
    @33
    @13
    @14
    wb
    @25
    @34
    @8
    @0
    @7
    @5
    @35
    @25
    @27
    @26
    cX
    @3
    cG
    @6
    @4
    gexex.1
    @28
    grpcl
    syl3anc
    @34
    cX
    @3
    cG
    @9
    @11
    @9
    gexex.1
    @28
    grplcan
    syl13anc
    mpbid
    isabld
end
