include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "csubg.mm"
include "wb.mm"
include "eqid.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "wa.mm"
include "cminusg.mm"
include "adantr.mm"
include "subginvcl.mm"
include "sylan.mm"
include "cbs.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wss.mm"
include "subgss.mm"
include "sselda.mm"
include "grpsubinv.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "grpsubval.mm"
include "impbid.mm"
include "rexbidva.mm"
include "bitrd.mm"

theorem lsmelvalm
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let vx: setvar x
  let cY: class Y
  assume lsmelvalm.m: |- .- = ( -g ` G )
  assume lsmelvalm.p: |- .(+) = ( LSSum ` G )
  assume lsmelvalm.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmelvalm.u: |- ( ph -> U e. ( SubGrp ` G ) )

  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint X y
  disjoint X z
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint G x
  disjoint ph x
  disjoint T x
  disjoint U x
  disjoint X x
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( X e. ( T .(+) U ) <-> E. y e. T E. z e. U X = ( y .- z ) ) )

  proof
    wph
    cX
    cT
    cU
    c.po
    co
    wcel
    #
    cX
    vy
    cv
    #
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vx
    cU
    wrex
    #
    vy
    cT
    wrex
    #
    cX
    @1
    vz
    cv
    #
    c.mi
    co
    #
    wceq
    #
    vz
    cU
    wrex
    #
    vy
    cT
    wrex
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @12
    wcel
    #
    @0
    @7
    wb
    lsmelvalm.t
    lsmelvalm.u
    vy
    vx
    @3
    c.po
    cT
    cU
    cG
    cX
    @3
    eqid
    #
    lsmelvalm.p
    lsmelval
    syl2anc
    wph
    @6
    @11
    vy
    cT
    wph
    @1
    cT
    wcel
    #
    wa
    #
    @6
    @11
    @17
    @5
    @11
    vx
    cU
    @17
    @2
    cU
    wcel
    #
    wa
    #
    @11
    @5
    @4
    @9
    wceq
    #
    vz
    cU
    wrex
    #
    @19
    @2
    cG
    cminusg
    cfv
    #
    cfv
    #
    cU
    wcel
    #
    @4
    @1
    @23
    c.mi
    co
    #
    wceq
    #
    @21
    @17
    @14
    @18
    @24
    wph
    @14
    @16
    lsmelvalm.u
    adantr
    #
    cU
    cG
    @22
    @2
    @22
    eqid
    #
    subginvcl
    sylan
    @19
    @25
    @4
    @19
    cG
    cbs
    cfv
    #
    @3
    cG
    c.mi
    @22
    @1
    @2
    @29
    eqid
    #
    @15
    lsmelvalm.m
    @28
    wph
    cG
    cgrp
    wcel
    #
    @16
    @18
    wph
    @13
    @31
    lsmelvalm.t
    cT
    cG
    subgrcl
    syl
    ad2antrr
    @17
    @1
    @29
    wcel
    #
    @18
    wph
    cT
    @29
    @1
    wph
    @13
    cT
    @29
    wss
    lsmelvalm.t
    @29
    cT
    cG
    @30
    subgss
    syl
    sselda
    #
    adantr
    @17
    cU
    @29
    @2
    @17
    @14
    cU
    @29
    wss
    @27
    @29
    cU
    cG
    @30
    subgss
    syl
    #
    sselda
    grpsubinv
    eqcomd
    @20
    @26
    vz
    @23
    cU
    @8
    @23
    wceq
    @9
    @25
    @4
    @8
    @23
    @1
    c.mi
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @5
    @10
    @20
    vz
    cU
    cX
    @4
    @9
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    @17
    @10
    @6
    vz
    cU
    @17
    @8
    cU
    wcel
    #
    wa
    #
    @6
    @10
    @9
    @4
    wceq
    #
    vx
    cU
    wrex
    #
    @36
    @8
    @22
    cfv
    #
    cU
    wcel
    #
    @9
    @1
    @39
    @3
    co
    #
    wceq
    #
    @38
    @17
    @14
    @35
    @40
    @27
    cU
    cG
    @22
    @8
    @28
    subginvcl
    sylan
    @36
    @32
    @8
    @29
    wcel
    @42
    @17
    @32
    @35
    @33
    adantr
    @17
    cU
    @29
    @8
    @34
    sselda
    @29
    @3
    cG
    @22
    c.mi
    @1
    @8
    @30
    @15
    @28
    lsmelvalm.m
    grpsubval
    syl2anc
    @37
    @42
    vx
    @39
    cU
    @2
    @39
    wceq
    @4
    @41
    @9
    @2
    @39
    @1
    @3
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @10
    @5
    @37
    vx
    cU
    cX
    @9
    @4
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    impbid
    rexbidva
    bitrd
end
