include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "cc.mm"
include "cbs.mm"
include "eqid.mm"
include "cn.mm"
include "cabl.mm"
include "cgrp.mm"
include "dchrabl.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "4syl.mm"
include "dchrf.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "simpr.mm"
include "0re.mm"
include "syl6eqel.mm"
include "wne.mm"
include "c1.mm"
include "cui.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "dchrn0.mm"
include "biimpa.mm"
include "dchr1.mm"
include "1re.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem dchr1re
  let wph: wff ph
  let cB: class B
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  assume dchr1re.g: |- G = ( DChr ` N )
  assume dchr1re.z: |- Z = ( Z/nZ ` N )
  assume dchr1re.o: |- .1. = ( 0g ` G )
  assume dchr1re.b: |- B = ( Base ` Z )
  assume dchr1re.n: |- ( ph -> N e. NN )


  assert |- ( ph -> .1. : B --> RR )

  proof
    wph
    c.1
    cB
    wfn
    #
    vx
    cv
    #
    c.1
    cfv
    #
    cr
    wcel
    #
    vx
    cB
    wral
    cB
    cr
    c.1
    wf
    wph
    cB
    cc
    c.1
    wf
    @0
    wph
    cB
    cG
    cbs
    cfv
    #
    cG
    cN
    c.1
    cZ
    dchr1re.g
    dchr1re.z
    @4
    eqid
    #
    dchr1re.b
    wph
    cN
    cn
    wcel
    #
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    c.1
    @4
    wcel
    #
    dchr1re.n
    cG
    cN
    dchr1re.g
    dchrabl
    cG
    ablgrp
    @4
    cG
    c.1
    @5
    dchr1re.o
    grpidcl
    4syl
    #
    dchrf
    cB
    cc
    c.1
    ffn
    syl
    wph
    @3
    vx
    cB
    wph
    @1
    cB
    wcel
    #
    wa
    #
    @3
    @2
    cc0
    @10
    @2
    cc0
    wceq
    #
    wa
    @2
    cc0
    cr
    @10
    @11
    simpr
    0re
    syl6eqel
    @10
    @2
    cc0
    wne
    #
    wa
    #
    @2
    c1
    cr
    @13
    @1
    cZ
    cui
    cfv
    #
    c.1
    cG
    cN
    cZ
    dchr1re.g
    dchr1re.z
    dchr1re.o
    @14
    eqid
    #
    wph
    @6
    @9
    @12
    dchr1re.n
    ad2antrr
    @10
    @12
    @1
    @14
    wcel
    @10
    @1
    cB
    @4
    @14
    cG
    cN
    c.1
    cZ
    dchr1re.g
    dchr1re.z
    @5
    dchr1re.b
    @15
    wph
    @7
    @9
    @8
    adantr
    wph
    @9
    simpr
    dchrn0
    biimpa
    dchr1
    1re
    syl6eqel
    pm2.61dane
    ralrimiva
    vx
    cB
    cr
    c.1
    ffnfv
    sylanbrc
end
