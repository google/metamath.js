include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cgim.mm"
include "cplusg.mm"
include "eqid.mm"
include "cgrp.mm"
include "c0g.mm"
include "wceq.mm"
include "eqidd.mm"
include "wfo.mm"
include "f1ofo.mm"
include "syl.mm"
include "cv.mm"
include "f1ocpbl.mm"
include "imasgrp.mm"
include "simpld.mm"
include "wf.mm"
include "wb.mm"
include "imasbas.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "f1oeq2.mm"
include "f1of.mm"
include "wa.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "w3a.mm"
include "imasaddval.mm"
include "eqcomd.mm"
include "3expib.mm"
include "sylbird.mm"
include "imp.mm"
include "isghmd.mm"
include "isgim.mm"
include "sylanbrc.mm"

theorem imasgim
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume imasgim.u: |- ( ph -> U = ( F "s R ) )
  assume imasgim.v: |- ( ph -> V = ( Base ` R ) )
  assume imasgim.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasgim.r: |- ( ph -> R e. Grp )


  assert |- ( ph -> F e. ( R GrpIso U ) )

  proof
    wph
    cF
    cR
    cU
    cghm
    co
    wcel
    cR
    cbs
    cfv
    #
    cU
    cbs
    cfv
    #
    cF
    wf1o
    #
    cF
    cR
    cU
    cgim
    co
    wcel
    wph
    va
    vb
    cR
    cplusg
    cfv
    #
    cU
    cplusg
    cfv
    #
    cR
    cU
    cF
    @0
    @1
    @0
    eqid
    #
    @1
    eqid
    #
    @3
    eqid
    #
    @4
    eqid
    #
    imasgim.r
    wph
    cU
    cgrp
    wcel
    cR
    c0g
    cfv
    #
    cF
    cfv
    cU
    c0g
    cfv
    wceq
    wph
    cB
    @3
    cR
    cU
    cF
    cV
    @9
    vd
    vc
    va
    vb
    imasgim.u
    imasgim.v
    wph
    @3
    eqidd
    wph
    cV
    cB
    cF
    wf1o
    #
    cV
    cB
    cF
    wfo
    imasgim.f
    cV
    cB
    cF
    f1ofo
    syl
    #
    wph
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    vd
    cv
    @3
    cF
    cV
    cB
    imasgim.f
    f1ocpbl
    #
    imasgim.r
    @9
    eqid
    imasgrp
    simpld
    wph
    @2
    @0
    @1
    cF
    wf
    wph
    cV
    @1
    cF
    wf1o
    #
    @2
    wph
    @10
    @15
    imasgim.f
    wph
    cB
    @1
    wceq
    @10
    @15
    wb
    wph
    cB
    cR
    cU
    cF
    cV
    cgrp
    imasgim.u
    imasgim.v
    @11
    imasgim.r
    imasbas
    cB
    @1
    cV
    cF
    f1oeq3
    syl
    mpbid
    wph
    cV
    @0
    wceq
    @15
    @2
    wb
    imasgim.v
    cV
    @0
    @1
    cF
    f1oeq2
    syl
    mpbid
    #
    @0
    @1
    cF
    f1of
    syl
    wph
    @12
    @0
    wcel
    #
    @13
    @0
    wcel
    #
    wa
    #
    @12
    @13
    @3
    co
    cF
    cfv
    #
    @12
    cF
    cfv
    @13
    cF
    cfv
    @4
    co
    #
    wceq
    #
    wph
    @19
    @12
    cV
    wcel
    #
    @13
    cV
    wcel
    #
    wa
    @22
    wph
    @23
    @17
    @24
    @18
    wph
    cV
    @0
    @12
    imasgim.v
    eleq2d
    wph
    cV
    @0
    @13
    imasgim.v
    eleq2d
    anbi12d
    wph
    @23
    @24
    @22
    wph
    @23
    @24
    w3a
    @21
    @20
    wph
    cB
    cR
    @4
    @3
    cU
    cF
    cV
    @12
    @13
    cgrp
    vd
    vc
    va
    vb
    @11
    @14
    imasgim.u
    imasgim.v
    imasgim.r
    @7
    @8
    imasaddval
    eqcomd
    3expib
    sylbird
    imp
    isghmd
    @16
    @0
    @1
    cR
    cU
    cF
    @5
    @6
    isgim
    sylanbrc
end
