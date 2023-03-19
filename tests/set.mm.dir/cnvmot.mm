include "ccnv.mm"
include "cismt.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "motf1o.mm"
include "f1ocnv.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "wf.mm"
include "f1of.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "motcgr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "ismot.mm"
include "mpbir2and.mm"

theorem cnvmot
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motco.2: |- ( ph -> F e. ( G Ismt G ) )


  assert |- ( ph -> `' F e. ( G Ismt G ) )

  proof
    wph
    cF
    ccnv
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
    #
    cP
    cP
    cF
    f1ocnv
    syl
    #
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
    @5
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    c.mi
    co
    @8
    @9
    @18
    @5
    @7
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
    @17
    motgrp.1
    adantr
    @18
    cP
    cP
    @4
    @0
    wph
    cP
    cP
    @0
    wf
    #
    @17
    wph
    @3
    @22
    @14
    cP
    cP
    @0
    f1of
    syl
    adantr
    #
    wph
    @15
    @16
    simprl
    #
    ffvelrnd
    @18
    cP
    cP
    @6
    @0
    @23
    wph
    @15
    @16
    simprr
    #
    ffvelrnd
    wph
    cF
    @1
    wcel
    @17
    motco.2
    adantr
    motcgr
    @18
    @19
    @4
    @20
    @6
    c.mi
    @18
    @12
    @15
    @19
    @4
    wceq
    wph
    @12
    @17
    @13
    adantr
    #
    @24
    cP
    cP
    @4
    cF
    f1ocnvfv2
    syl2anc
    @18
    @12
    @16
    @20
    @6
    wceq
    @26
    @25
    cP
    cP
    @6
    cF
    f1ocnvfv2
    syl2anc
    oveq12d
    eqtr3d
    ralrimivva
    wph
    @21
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
