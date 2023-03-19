include "cfv.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "eqid.mm"
include "mvrcl2.mm"
include "cvv.mm"
include "wfun.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "csn.mm"
include "cfn.mm"
include "csupp.mm"
include "wss.mm"
include "fvexd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "wf.mm"
include "psrelbas.mm"
include "ffun.mm"
include "syl.mm"
include "snfi.mm"
include "a1i.mm"
include "cdif.mm"
include "wa.mm"
include "cur.mm"
include "crg.mm"
include "adantr.mm"
include "wne.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "mvrval2.mm"
include "simprd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "suppss.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "mplelbas.mm"
include "sylanbrc.mm"

theorem mvrcl
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume mvrcl.s: |- P = ( I mPoly R )
  assume mvrcl.v: |- V = ( I mVar R )
  assume mvrcl.b: |- B = ( Base ` P )
  assume mvrcl.i: |- ( ph -> I e. W )
  assume mvrcl.r: |- ( ph -> R e. Ring )
  assume mvrcl.x: |- ( ph -> X e. I )


  assert |- ( ph -> ( V ` X ) e. B )

  proof
    wph
    cX
    cV
    cfv
    #
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    wcel
    @0
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @0
    cB
    wcel
    wph
    @2
    cR
    @1
    cI
    cV
    cW
    cX
    @1
    eqid
    #
    mvrcl.v
    @2
    eqid
    #
    mvrcl.i
    mvrcl.r
    mvrcl.x
    mvrcl2
    #
    wph
    @0
    cvv
    wcel
    @0
    wfun
    #
    @3
    cvv
    wcel
    vy
    cI
    vy
    cv
    cX
    wceq
    c1
    cc0
    cif
    cmpt
    #
    csn
    #
    cfn
    wcel
    #
    @0
    @3
    csupp
    co
    @10
    wss
    @4
    wph
    cX
    cV
    fvexd
    wph
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    cR
    cbs
    cfv
    #
    @0
    wf
    @8
    wph
    @2
    @12
    cR
    @1
    vf
    cI
    @13
    @0
    @5
    @13
    eqid
    @12
    eqid
    #
    @6
    @7
    psrelbas
    #
    @12
    @13
    @0
    ffun
    syl
    wph
    cR
    c0g
    fvexd
    @11
    wph
    @9
    snfi
    a1i
    wph
    @12
    @13
    vx
    @0
    @10
    @3
    @15
    wph
    vx
    cv
    #
    @12
    @10
    cdif
    wcel
    #
    wa
    #
    @16
    @0
    cfv
    @16
    @9
    wceq
    #
    cR
    cur
    cfv
    #
    @3
    cif
    @3
    @18
    vy
    @12
    cR
    @20
    vf
    @16
    cI
    cV
    cW
    cX
    crg
    @3
    mvrcl.v
    @14
    @3
    eqid
    #
    @20
    eqid
    wph
    cI
    cW
    wcel
    @17
    mvrcl.i
    adantr
    wph
    cR
    crg
    wcel
    @17
    mvrcl.r
    adantr
    wph
    cX
    cI
    wcel
    @17
    mvrcl.x
    adantr
    @18
    @16
    @12
    wcel
    #
    @16
    @9
    wne
    #
    @18
    @17
    @22
    @23
    wa
    wph
    @17
    simpr
    @16
    @12
    @9
    eldifsn
    sylib
    #
    simpld
    mvrval2
    @18
    @19
    @20
    @3
    @18
    @16
    @9
    @18
    @22
    @23
    @24
    simprd
    neneqd
    iffalsed
    eqtrd
    suppss
    @10
    @0
    cvv
    cvv
    @3
    suppssfifsupp
    syl32anc
    @2
    cP
    cR
    @1
    cB
    cI
    @0
    @3
    mvrcl.s
    @5
    @6
    @21
    mvrcl.b
    mplelbas
    sylanbrc
end
