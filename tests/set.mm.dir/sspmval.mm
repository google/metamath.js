include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "wceq.mm"
include "wi.mm"
include "sspnv.mm"
include "cc.mm"
include "neg1cn.mm"
include "eqid.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "ex.mm"
include "syl.mm"
include "anim2d.mm"
include "imp.mm"
include "sspgval.mm"
include "syldan.mm"
include "sspsval.mm"
include "mpanr1.mm"
include "adantrl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "nvmval.mm"
include "3expb.mm"
include "sylan.mm"
include "cba.mm"
include "sspba.mm"
include "sseld.mm"
include "anim12d.mm"
include "adantlr.mm"
include "3eqtr4d.mm"

theorem sspmval
  let cA: class A
  let cB: class B
  let cU: class U
  let cH: class H
  let cL: class L
  let cM: class M
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspm.y: |- Y = ( BaseSet ` W )
  assume sspm.m: |- M = ( -v ` U )
  assume sspm.l: |- L = ( -v ` W )
  assume sspm.h: |- H = ( SubSp ` U )


  assert |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) -> ( A L B ) = ( A M B ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cA
    cY
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    wa
    #
    cA
    c1
    cneg
    #
    cB
    cW
    cns
    cfv
    #
    co
    #
    cW
    cpv
    cfv
    #
    co
    #
    cA
    @7
    cB
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cA
    cB
    cL
    co
    #
    cA
    cB
    cM
    co
    #
    @6
    @11
    cA
    @9
    @14
    co
    #
    @15
    @2
    @5
    @3
    @9
    cY
    wcel
    #
    wa
    #
    @11
    @18
    wceq
    @2
    @5
    @20
    @2
    @4
    @19
    @3
    @2
    cW
    cnv
    wcel
    #
    @4
    @19
    wi
    cU
    cH
    cW
    sspm.h
    sspnv
    #
    @21
    @4
    @19
    @21
    @7
    cc
    wcel
    #
    @4
    @19
    neg1cn
    @7
    cB
    @8
    cW
    cY
    sspm.y
    @8
    eqid
    #
    nvscl
    mp3an2
    ex
    syl
    anim2d
    imp
    cA
    @9
    cU
    @10
    @14
    cH
    cW
    cY
    sspm.y
    @14
    eqid
    #
    @10
    eqid
    #
    sspm.h
    sspgval
    syldan
    @6
    @9
    @13
    cA
    @14
    @2
    @4
    @9
    @13
    wceq
    #
    @3
    @2
    @23
    @4
    @27
    neg1cn
    @7
    cB
    @8
    @12
    cU
    cH
    cW
    cY
    sspm.y
    @12
    eqid
    #
    @24
    sspm.h
    sspsval
    mpanr1
    adantrl
    oveq2d
    eqtrd
    @2
    @21
    @5
    @16
    @11
    wceq
    #
    @22
    @21
    @3
    @4
    @29
    cA
    cB
    @8
    cW
    @10
    cL
    cY
    sspm.y
    @26
    @24
    sspm.l
    nvmval
    3expb
    sylan
    @2
    @5
    cA
    cU
    cba
    cfv
    #
    wcel
    #
    cB
    @30
    wcel
    #
    wa
    #
    @17
    @15
    wceq
    #
    @2
    @5
    @33
    @2
    @3
    @31
    @4
    @32
    @2
    cY
    @30
    cA
    cU
    cH
    cW
    @30
    cY
    @30
    eqid
    #
    sspm.y
    sspm.h
    sspba
    #
    sseld
    @2
    cY
    @30
    cB
    @36
    sseld
    anim12d
    imp
    @0
    @33
    @34
    @1
    @0
    @31
    @32
    @34
    cA
    cB
    @12
    cU
    @14
    cM
    @30
    @35
    @25
    @28
    sspm.m
    nvmval
    3expb
    adantlr
    syldan
    3eqtr4d
end
