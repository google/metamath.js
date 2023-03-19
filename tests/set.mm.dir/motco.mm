include "ccom.mm"
include "cismt.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "motf1o.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "wa.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "fvco3.mm"
include "simprr.mm"
include "oveq12d.mm"
include "ffvelrnd.mm"
include "motcgr.mm"
include "3eqtrd.mm"
include "ralrimivva.mm"
include "wb.mm"
include "ismot.mm"
include "mpbir2and.mm"

theorem motco
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motco.2: |- ( ph -> F e. ( G Ismt G ) )
  assume motco.3: |- ( ph -> H e. ( G Ismt G ) )


  assert |- ( ph -> ( F o. H ) e. ( G Ismt G ) )

  proof
    wph
    cF
    cH
    ccom
    #
    cG
    cG
    cismt
    co
    #
    wcel
    #
    cP
    cP
    @0
    wf1o
    #
    va
    cv
    #
    @0
    cfv
    #
    vb
    cv
    #
    @0
    cfv
    #
    c.mi
    co
    #
    @4
    @6
    c.mi
    co
    #
    wceq
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    wph
    cP
    cP
    cF
    wf1o
    cP
    cP
    cH
    wf1o
    #
    @3
    wph
    cP
    cF
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motgrp.1
    motco.2
    motf1o
    wph
    cP
    cH
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motgrp.1
    motco.3
    motf1o
    #
    cP
    cP
    cP
    cF
    cH
    f1oco
    syl2anc
    wph
    @10
    va
    vb
    cP
    cP
    wph
    @4
    cP
    wcel
    #
    @6
    cP
    wcel
    #
    wa
    #
    wa
    #
    @8
    @4
    cH
    cfv
    #
    cF
    cfv
    #
    @6
    cH
    cfv
    #
    cF
    cfv
    #
    c.mi
    co
    @18
    @20
    c.mi
    co
    @9
    @17
    @5
    @19
    @7
    @21
    c.mi
    @17
    cP
    cP
    cH
    wf
    #
    @14
    @5
    @19
    wceq
    wph
    @22
    @16
    wph
    @12
    @22
    @13
    cP
    cP
    cH
    f1of
    syl
    adantr
    #
    wph
    @14
    @15
    simprl
    #
    cP
    cP
    @4
    cF
    cH
    fvco3
    syl2anc
    @17
    @22
    @15
    @7
    @21
    wceq
    @23
    wph
    @14
    @15
    simprr
    #
    cP
    cP
    @6
    cF
    cH
    fvco3
    syl2anc
    oveq12d
    @17
    @18
    @20
    cP
    cF
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    wph
    cG
    cV
    wcel
    #
    @16
    motgrp.1
    adantr
    #
    @17
    cP
    cP
    @4
    cH
    @23
    @24
    ffvelrnd
    @17
    cP
    cP
    @6
    cH
    @23
    @25
    ffvelrnd
    wph
    cF
    @1
    wcel
    @16
    motco.2
    adantr
    motcgr
    @17
    @4
    @6
    cP
    cH
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    @27
    @24
    @25
    wph
    cH
    @1
    wcel
    @16
    motco.3
    adantr
    motcgr
    3eqtrd
    ralrimivva
    wph
    @26
    @2
    @3
    @11
    wa
    wb
    motgrp.1
    cP
    @0
    cG
    c.mi
    cV
    va
    vb
    ismot.p
    ismot.m
    ismot
    syl
    mpbir2and
end
