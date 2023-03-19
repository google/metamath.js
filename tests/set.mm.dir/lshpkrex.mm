include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "clsm.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "wrex.mm"
include "clss.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "lveclmod.mm"
include "islshpsm.mm"
include "simp3.mm"
include "syl6bi.mm"
include "imp.mm"
include "cvsca.mm"
include "cplusg.mm"
include "csca.mm"
include "crio.mm"
include "cmpt.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "lshpkrcl.mm"
include "lshpkr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lshpkrex
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume lshpkrex.h: |- H = ( LSHyp ` W )
  assume lshpkrex.f: |- F = ( LFnl ` W )
  assume lshpkrex.k: |- K = ( LKer ` W )

  disjoint F g
  disjoint K g
  disjoint U g
  disjoint W g
  disjoint g z
  disjoint F z
  disjoint H z
  disjoint K z
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint U k
  disjoint x y
  disjoint x z
  disjoint U x
  disjoint y z
  disjoint U y
  disjoint U z
  disjoint W k
  disjoint W x
  disjoint W y
  disjoint W z
  assert |- ( ( W e. LVec /\ U e. H ) -> E. g e. F ( K ` g ) = U )

  proof
    cW
    clvec
    wcel
    #
    cU
    cH
    wcel
    #
    wa
    #
    cU
    vz
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    cW
    clsm
    cfv
    #
    co
    cW
    cbs
    cfv
    #
    wceq
    #
    vz
    @6
    wrex
    #
    vg
    cv
    #
    cK
    cfv
    #
    cU
    wceq
    #
    vg
    cF
    wrex
    #
    @0
    @1
    @8
    @0
    @1
    cU
    cW
    clss
    cfv
    #
    wcel
    #
    cU
    @6
    wne
    #
    @8
    w3a
    @8
    @0
    vz
    @5
    @13
    cU
    cH
    @4
    @6
    cW
    @6
    eqid
    #
    @4
    eqid
    #
    @13
    eqid
    @5
    eqid
    #
    lshpkrex.h
    cW
    lveclmod
    islshpsm
    @14
    @15
    @8
    simp3
    syl6bi
    imp
    @2
    @7
    @12
    vz
    @6
    @2
    @3
    @6
    wcel
    #
    @7
    w3a
    #
    vx
    @6
    vx
    cv
    vy
    cv
    vk
    cv
    @3
    cW
    cvsca
    cfv
    #
    co
    cW
    cplusg
    cfv
    #
    co
    wceq
    vy
    cU
    wrex
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    crio
    cmpt
    #
    cF
    wcel
    @25
    cK
    cfv
    #
    cU
    wceq
    #
    @12
    @20
    vx
    vy
    @23
    @22
    @5
    @21
    cU
    vk
    cF
    @25
    cH
    @24
    @4
    @6
    cW
    @3
    @16
    @22
    eqid
    #
    @17
    @18
    lshpkrex.h
    @0
    @1
    @19
    @7
    simp1l
    #
    @0
    @1
    @19
    @7
    simp1r
    #
    @2
    @19
    @7
    simp2
    #
    @2
    @19
    @7
    simp3
    #
    @23
    eqid
    #
    @24
    eqid
    #
    @21
    eqid
    #
    @25
    eqid
    #
    lshpkrex.f
    lshpkrcl
    @20
    vx
    vy
    @23
    @22
    @5
    @21
    cU
    vk
    @25
    cH
    @24
    cK
    @4
    @6
    cW
    @3
    @16
    @28
    @17
    @18
    lshpkrex.h
    @29
    @30
    @31
    @32
    @33
    @34
    @35
    @36
    lshpkrex.k
    lshpkr
    @11
    @27
    vg
    @25
    cF
    @9
    @25
    wceq
    @10
    @26
    cU
    @9
    @25
    cK
    fveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdv3a
    mpd
end
