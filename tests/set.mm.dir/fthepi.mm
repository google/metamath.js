include "coppc.mm"
include "cfv.mm"
include "cmon.mm"
include "co.mm"
include "ctpos.mm"
include "chom.mm"
include "eqid.mm"
include "oppcbas.mm"
include "fthoppc.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "ovtpos.mm"
include "fveq1i.mm"
include "syl5eqel.mm"
include "ccat.mm"
include "wcel.mm"
include "cop.mm"
include "cfunc.mm"
include "wa.mm"
include "wbr.mm"
include "cfth.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "syl.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "simprd.mm"
include "oppcmon.mm"
include "eleqtrrd.mm"
include "fthmon.mm"
include "simpld.mm"
include "eleqtrd.mm"

theorem fthepi
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cI: class I
  let cJ: class J
  assume fthmon.b: |- B = ( Base ` C )
  assume fthmon.h: |- H = ( Hom ` C )
  assume fthmon.f: |- ( ph -> F ( C Faith D ) G )
  assume fthmon.x: |- ( ph -> X e. B )
  assume fthmon.y: |- ( ph -> Y e. B )
  assume fthmon.r: |- ( ph -> R e. ( X H Y ) )
  assume fthepi.e: |- E = ( Epi ` C )
  assume fthepi.p: |- P = ( Epi ` D )
  assume fthepi.1: |- ( ph -> ( ( X G Y ) ` R ) e. ( ( F ` X ) P ( F ` Y ) ) )


  assert |- ( ph -> R e. ( X E Y ) )

  proof
    wph
    cR
    cY
    cX
    cC
    coppc
    cfv
    #
    cmon
    cfv
    #
    co
    cX
    cY
    cE
    co
    wph
    cB
    @0
    cD
    coppc
    cfv
    #
    cR
    cF
    cG
    ctpos
    #
    @0
    chom
    cfv
    #
    @1
    @2
    cmon
    cfv
    #
    cY
    cX
    cB
    cC
    @0
    @0
    eqid
    #
    fthmon.b
    oppcbas
    @4
    eqid
    wph
    cC
    cD
    @2
    cF
    cG
    @0
    @6
    @2
    eqid
    #
    fthmon.f
    fthoppc
    fthmon.y
    fthmon.x
    wph
    cR
    cX
    cY
    cH
    co
    cY
    cX
    @4
    co
    fthmon.r
    cC
    cH
    @0
    cY
    cX
    fthmon.h
    @6
    oppchom
    syl6eleqr
    @1
    eqid
    #
    @5
    eqid
    #
    wph
    cR
    cY
    cX
    @3
    co
    #
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cP
    co
    #
    @13
    @12
    @5
    co
    wph
    @11
    cR
    cX
    cY
    cG
    co
    #
    cfv
    @14
    cR
    @10
    @15
    cY
    cX
    cG
    ovtpos
    fveq1i
    fthepi.1
    syl5eqel
    wph
    cD
    cP
    @5
    @2
    @13
    @12
    @7
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @16
    @17
    wa
    wph
    cF
    cG
    @19
    wbr
    #
    @20
    wph
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    @21
    fthmon.f
    @22
    @19
    cF
    cG
    cC
    cD
    fthfunc
    ssbri
    syl
    cF
    cG
    @19
    df-br
    sylib
    cC
    cD
    @18
    funcrcl
    syl
    #
    simprd
    @9
    fthepi.p
    oppcmon
    eleqtrrd
    fthmon
    wph
    cC
    cE
    @1
    @0
    cY
    cX
    @6
    wph
    @16
    @17
    @23
    simpld
    @8
    fthepi.e
    oppcmon
    eleqtrd
end
