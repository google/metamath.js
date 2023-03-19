include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cplusg.mm"
include "cvsca.mm"
include "csn.mm"
include "eqidd.mm"
include "clss.mm"
include "wceq.mm"
include "a1i.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "snssd.mm"
include "c0.mm"
include "wne.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snnz.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "simpr2.mm"
include "elsni.mm"
include "syl.mm"
include "oveq2d.mm"
include "lmodvs0.mm"
include "3ad2antr1.mm"
include "eqtrd.mm"
include "simpr3.mm"
include "oveq12d.mm"
include "lmod0vlid.mm"
include "mpdan.mm"
include "adantr.mm"
include "ovex.mm"
include "elsn.mm"
include "sylibr.mm"
include "islssd.mm"

theorem lsssn0
  let cS: class S
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let cX: class X
  let vy: setvar y
  assume lss0cl.z: |- .0. = ( 0g ` W )
  assume lss0cl.s: |- S = ( LSubSp ` W )


  assert |- ( W e. LMod -> { .0. } e. S )

  proof
    cW
    clmod
    wcel
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cplusg
    cfv
    #
    cS
    cW
    cvsca
    cfv
    #
    c.0
    csn
    #
    @1
    cW
    cbs
    cfv
    #
    cW
    va
    vb
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    @0
    @6
    eqidd
    @0
    @3
    eqidd
    @0
    @4
    eqidd
    cS
    cW
    clss
    cfv
    wceq
    @0
    lss0cl.s
    a1i
    @0
    c.0
    @6
    @6
    cW
    c.0
    @6
    eqid
    #
    lss0cl.z
    lmod0vcl
    #
    snssd
    @5
    c0
    wne
    @0
    c.0
    c.0
    cW
    c0g
    cfv
    cvv
    lss0cl.z
    cW
    c0g
    fvex
    eqeltri
    snnz
    a1i
    @0
    vx
    cv
    #
    @2
    wcel
    #
    va
    cv
    #
    @5
    wcel
    #
    vb
    cv
    #
    @5
    wcel
    #
    w3a
    #
    wa
    #
    @9
    @11
    @4
    co
    #
    @13
    @3
    co
    #
    c.0
    wceq
    @18
    @5
    wcel
    @16
    @18
    c.0
    c.0
    @3
    co
    #
    c.0
    @16
    @17
    c.0
    @13
    c.0
    @3
    @16
    @17
    @9
    c.0
    @4
    co
    #
    c.0
    @16
    @11
    c.0
    @9
    @4
    @16
    @12
    @11
    c.0
    wceq
    @0
    @10
    @12
    @14
    simpr2
    @11
    c.0
    elsni
    syl
    oveq2d
    @0
    @12
    @10
    @20
    c.0
    wceq
    @14
    @4
    @1
    @2
    cW
    @9
    c.0
    @1
    eqid
    @4
    eqid
    @2
    eqid
    lss0cl.z
    lmodvs0
    3ad2antr1
    eqtrd
    @16
    @14
    @13
    c.0
    wceq
    @0
    @10
    @12
    @14
    simpr3
    @13
    c.0
    elsni
    syl
    oveq12d
    @0
    @19
    c.0
    wceq
    #
    @15
    @0
    c.0
    @6
    wcel
    @21
    @8
    @3
    @6
    cW
    c.0
    c.0
    @7
    @3
    eqid
    lss0cl.z
    lmod0vlid
    mpdan
    adantr
    eqtrd
    @18
    c.0
    @17
    @13
    @3
    ovex
    elsn
    sylibr
    islssd
end
