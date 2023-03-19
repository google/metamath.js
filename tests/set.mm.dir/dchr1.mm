include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cmpt.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "dchr1cl.mm"
include "eleq1.mm"
include "ifbid.mm"
include "cbvmptv.mm"
include "dchrmulid2.mm"
include "cn.mm"
include "cabl.mm"
include "cgrp.mm"
include "wa.mm"
include "wb.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "isgrpid2.mm"
include "4syl.mm"
include "mpbi2and.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "iftrued.mm"
include "unitss.mm"
include "sseldi.mm"
include "1cnd.mm"
include "fvmptd.mm"

theorem dchr1
  let wph: wff ph
  let cA: class A
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume dchr1.g: |- G = ( DChr ` N )
  assume dchr1.z: |- Z = ( Z/nZ ` N )
  assume dchr1.o: |- .1. = ( 0g ` G )
  assume dchr1.u: |- U = ( Unit ` Z )
  assume dchr1.n: |- ( ph -> N e. NN )
  assume dchr1.a: |- ( ph -> A e. U )


  assert |- ( ph -> ( .1. ` A ) = 1 )

  proof
    wph
    vk
    cA
    vk
    cv
    #
    cU
    wcel
    #
    c1
    cc0
    cif
    #
    c1
    cZ
    cbs
    cfv
    #
    c.1
    cc
    wph
    vk
    @3
    @2
    cmpt
    #
    cG
    cbs
    cfv
    #
    wcel
    #
    @4
    @4
    cG
    cplusg
    cfv
    #
    co
    @4
    wceq
    #
    c.1
    @4
    wceq
    #
    wph
    @3
    @5
    cU
    @4
    vk
    cG
    cN
    cZ
    dchr1.g
    dchr1.z
    @5
    eqid
    #
    @3
    eqid
    #
    dchr1.u
    @4
    eqid
    dchr1.n
    dchr1cl
    #
    wph
    @3
    @5
    @7
    cU
    @4
    vx
    cG
    cN
    @4
    cZ
    dchr1.g
    dchr1.z
    @10
    @11
    dchr1.u
    vk
    vx
    @3
    @2
    vx
    cv
    #
    cU
    wcel
    #
    c1
    cc0
    cif
    @0
    @13
    wceq
    @1
    @14
    c1
    cc0
    @0
    @13
    cU
    eleq1
    ifbid
    cbvmptv
    @7
    eqid
    #
    @12
    dchrmulid2
    wph
    cN
    cn
    wcel
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @6
    @8
    wa
    @9
    wb
    dchr1.n
    cG
    cN
    dchr1.g
    dchrabl
    cG
    ablgrp
    @5
    @7
    cG
    c.1
    @4
    @10
    @15
    dchr1.o
    isgrpid2
    4syl
    mpbi2and
    wph
    @0
    cA
    wceq
    #
    wa
    #
    @1
    c1
    cc0
    @17
    @0
    cA
    cU
    wph
    @16
    simpr
    wph
    cA
    cU
    wcel
    @16
    dchr1.a
    adantr
    eqeltrd
    iftrued
    wph
    cU
    @3
    cA
    @3
    cZ
    cU
    @11
    dchr1.u
    unitss
    dchr1.a
    sseldi
    wph
    1cnd
    fvmptd
end
