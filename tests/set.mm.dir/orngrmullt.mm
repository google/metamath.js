include "co.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "corng.mm"
include "wcel.mm"
include "w3a.mm"
include "pltle.mm"
include "imp.mm"
include "syl31anc.mm"
include "crg.mm"
include "cgrp.mm"
include "orngring.mm"
include "syl.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "orngrmulle.mm"
include "wceq.mm"
include "wa.mm"
include "cdvr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cui.mm"
include "cdr.mm"
include "pltne.mm"
include "necomd.mm"
include "drngunit.mm"
include "biimpar.mm"
include "syl12anc.mm"
include "dvrcan3.mm"
include "syl3anc.mm"
include "adantr.mm"
include "3eqtr3d.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "wb.mm"
include "ringcl.mm"
include "pltval.mm"
include "mpbir2and.mm"

theorem orngrmullt
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.lt: class .<
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume ornglmullt.b: |- B = ( Base ` R )
  assume ornglmullt.t: |- .x. = ( .r ` R )
  assume ornglmullt.0: |- .0. = ( 0g ` R )
  assume ornglmullt.1: |- ( ph -> R e. oRing )
  assume ornglmullt.2: |- ( ph -> X e. B )
  assume ornglmullt.3: |- ( ph -> Y e. B )
  assume ornglmullt.4: |- ( ph -> Z e. B )
  assume ornglmullt.l: |- .< = ( lt ` R )
  assume ornglmullt.d: |- ( ph -> R e. DivRing )
  assume ornglmullt.5: |- ( ph -> X .< Y )
  assume ornglmullt.6: |- ( ph -> .0. .< Z )


  assert |- ( ph -> ( X .x. Z ) .< ( Y .x. Z ) )

  proof
    wph
    cX
    cZ
    c.x
    co
    #
    cY
    cZ
    c.x
    co
    #
    c.lt
    wbr
    #
    @0
    @1
    cR
    cple
    cfv
    #
    wbr
    #
    @0
    @1
    wne
    #
    wph
    cB
    cR
    c.x
    @3
    cX
    cY
    c.0
    cZ
    ornglmullt.b
    ornglmullt.t
    ornglmullt.0
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.4
    @3
    eqid
    #
    wph
    cR
    corng
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    @3
    wbr
    #
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.5
    @7
    @8
    @9
    w3a
    #
    @10
    @11
    corng
    cB
    cB
    c.lt
    cR
    @3
    cX
    cY
    @6
    ornglmullt.l
    pltle
    imp
    syl31anc
    wph
    @7
    c.0
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    c.0
    cZ
    c.lt
    wbr
    #
    c.0
    cZ
    @3
    wbr
    #
    ornglmullt.1
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    @13
    wph
    @7
    @17
    ornglmullt.1
    cR
    orngring
    syl
    #
    cR
    ringgrp
    cB
    cR
    c.0
    ornglmullt.b
    ornglmullt.0
    grpidcl
    3syl
    #
    ornglmullt.4
    ornglmullt.6
    @7
    @13
    @14
    w3a
    #
    @15
    @16
    corng
    cB
    cB
    c.lt
    cR
    @3
    c.0
    cZ
    @6
    ornglmullt.l
    pltle
    imp
    syl31anc
    orngrmulle
    wph
    @0
    @1
    wph
    @0
    @1
    wceq
    #
    cX
    cY
    wceq
    wph
    @21
    wa
    #
    @0
    cZ
    cR
    cdvr
    cfv
    #
    co
    #
    @1
    cZ
    @23
    co
    #
    cX
    cY
    @22
    @0
    @1
    cZ
    @23
    wph
    @21
    simpr
    oveq1d
    wph
    @24
    cX
    wceq
    #
    @21
    wph
    @17
    @8
    cZ
    cR
    cui
    cfv
    #
    wcel
    #
    @26
    @18
    ornglmullt.2
    wph
    cR
    cdr
    wcel
    #
    @14
    cZ
    c.0
    wne
    #
    @28
    ornglmullt.d
    ornglmullt.4
    wph
    c.0
    cZ
    wph
    @7
    @13
    @14
    @15
    c.0
    cZ
    wne
    #
    ornglmullt.1
    @19
    ornglmullt.4
    ornglmullt.6
    @20
    @15
    @31
    corng
    cB
    cB
    c.lt
    cR
    c.0
    cZ
    ornglmullt.l
    pltne
    imp
    syl31anc
    necomd
    @29
    @28
    @14
    @30
    wa
    cB
    cR
    @27
    cZ
    c.0
    ornglmullt.b
    @27
    eqid
    #
    ornglmullt.0
    drngunit
    biimpar
    syl12anc
    #
    cB
    @23
    cR
    c.x
    @27
    cX
    cZ
    ornglmullt.b
    @32
    @23
    eqid
    #
    ornglmullt.t
    dvrcan3
    syl3anc
    adantr
    wph
    @25
    cY
    wceq
    #
    @21
    wph
    @17
    @9
    @28
    @35
    @18
    ornglmullt.3
    @33
    cB
    @23
    cR
    c.x
    @27
    cY
    cZ
    ornglmullt.b
    @32
    @34
    ornglmullt.t
    dvrcan3
    syl3anc
    adantr
    3eqtr3d
    @22
    cX
    cY
    wph
    cX
    cY
    wne
    #
    @21
    wph
    @7
    @8
    @9
    @10
    @36
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.5
    @12
    @10
    @36
    corng
    cB
    cB
    c.lt
    cR
    cX
    cY
    ornglmullt.l
    pltne
    imp
    syl31anc
    adantr
    neneqd
    pm2.65da
    neqned
    wph
    @7
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @2
    @4
    @5
    wa
    wb
    ornglmullt.1
    wph
    @17
    @8
    @14
    @37
    @18
    ornglmullt.2
    ornglmullt.4
    cB
    cR
    c.x
    cX
    cZ
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    wph
    @17
    @9
    @14
    @38
    @18
    ornglmullt.3
    ornglmullt.4
    cB
    cR
    c.x
    cY
    cZ
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    corng
    cB
    cB
    c.lt
    cR
    @3
    @0
    @1
    @6
    ornglmullt.l
    pltval
    syl3anc
    mpbir2and
end
