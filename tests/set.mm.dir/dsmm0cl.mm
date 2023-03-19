include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "cmnd.mm"
include "prdsmndd.mm"
include "eqid.mm"
include "mndidcl.mm"
include "syl.mm"
include "c0.mm"
include "wn.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "ccom.mm"
include "prds0g.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "fveq1d.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "fvco2.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "nne.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "cdsmm.mm"
include "co.mm"
include "dsmmelbas.mm"
include "mpbir2and.mm"

theorem dsmm0cl
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let c.pl: class .+
  let cJ: class J
  let cK: class K
  assume dsmmcl.p: |- P = ( S Xs_ R )
  assume dsmmcl.h: |- H = ( Base ` ( S (+)m R ) )
  assume dsmmcl.i: |- ( ph -> I e. W )
  assume dsmmcl.s: |- ( ph -> S e. V )
  assume dsmmcl.r: |- ( ph -> R : I --> Mnd )
  assume dsmm0cl.z: |- .0. = ( 0g ` P )


  assert |- ( ph -> .0. e. H )

  proof
    wph
    c.0
    cH
    wcel
    c.0
    cP
    cbs
    cfv
    #
    wcel
    #
    va
    cv
    #
    c.0
    cfv
    #
    @2
    cR
    cfv
    c0g
    cfv
    #
    wne
    #
    va
    cI
    crab
    #
    cfn
    wcel
    wph
    cP
    cmnd
    wcel
    @1
    wph
    cR
    cS
    cI
    cV
    cW
    cP
    dsmmcl.p
    dsmmcl.i
    dsmmcl.s
    dsmmcl.r
    prdsmndd
    @0
    cP
    c.0
    @0
    eqid
    #
    dsmm0cl.z
    mndidcl
    syl
    wph
    @6
    c0
    cfn
    wph
    @5
    wn
    #
    va
    cI
    wral
    @6
    c0
    wceq
    wph
    @8
    va
    cI
    wph
    @2
    cI
    wcel
    #
    wa
    #
    @3
    @4
    wceq
    @8
    @10
    @2
    c0g
    cR
    ccom
    #
    cfv
    #
    @3
    @4
    @10
    @2
    @11
    c.0
    wph
    @11
    c.0
    wceq
    @9
    wph
    @11
    cP
    c0g
    cfv
    c.0
    wph
    cR
    cS
    cI
    cV
    cW
    cP
    dsmmcl.p
    dsmmcl.i
    dsmmcl.s
    dsmmcl.r
    prds0g
    dsmm0cl.z
    syl6eqr
    adantr
    fveq1d
    wph
    cR
    cI
    wfn
    #
    @9
    @12
    @4
    wceq
    wph
    cI
    cmnd
    cR
    wf
    @13
    dsmmcl.r
    cI
    cmnd
    cR
    ffn
    syl
    #
    cI
    c0g
    cR
    @2
    fvco2
    sylan
    eqtr3d
    @3
    @4
    nne
    sylibr
    ralrimiva
    @5
    va
    cI
    rabeq0
    sylibr
    0fin
    syl6eqel
    wph
    @0
    cS
    cR
    cdsmm
    co
    #
    cP
    cR
    cS
    cH
    cI
    cW
    c.0
    va
    dsmmcl.p
    @15
    eqid
    @7
    dsmmcl.h
    dsmmcl.i
    @14
    dsmmelbas
    mpbir2and
end
