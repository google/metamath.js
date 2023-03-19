include "cop.mm"
include "coppc.mm"
include "cfv.mm"
include "cco.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "oppcco.mm"
include "eqeq12d.mm"
include "chom.mm"
include "cmon.mm"
include "oppcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "oppcmon.mm"
include "eleqtrrd.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "moni.mm"
include "bitr3d.mm"

theorem epii
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vg: setvar g
  let vz: setvar z
  let vf: setvar f
  let vh: setvar h
  assume isepi.b: |- B = ( Base ` C )
  assume isepi.h: |- H = ( Hom ` C )
  assume isepi.o: |- .x. = ( comp ` C )
  assume isepi.e: |- E = ( Epi ` C )
  assume isepi.c: |- ( ph -> C e. Cat )
  assume isepi.x: |- ( ph -> X e. B )
  assume isepi.y: |- ( ph -> Y e. B )
  assume epii.z: |- ( ph -> Z e. B )
  assume epii.f: |- ( ph -> F e. ( X E Y ) )
  assume epii.g: |- ( ph -> G e. ( Y H Z ) )
  assume epii.k: |- ( ph -> K e. ( Y H Z ) )


  assert |- ( ph -> ( ( G ( <. X , Y >. .x. Z ) F ) = ( K ( <. X , Y >. .x. Z ) F ) <-> G = K ) )

  proof
    wph
    cF
    cG
    cZ
    cY
    cop
    cX
    cC
    coppc
    cfv
    #
    cco
    cfv
    #
    co
    #
    co
    #
    cF
    cK
    @2
    co
    #
    wceq
    cG
    cF
    cX
    cY
    cop
    cZ
    c.x
    co
    #
    co
    #
    cK
    cF
    @5
    co
    #
    wceq
    cG
    cK
    wceq
    wph
    @3
    @6
    @4
    @7
    wph
    cB
    cC
    c.x
    cG
    cF
    @0
    cZ
    cY
    cX
    isepi.b
    isepi.o
    @0
    eqid
    #
    epii.z
    isepi.y
    isepi.x
    oppcco
    wph
    cB
    cC
    c.x
    cK
    cF
    @0
    cZ
    cY
    cX
    isepi.b
    isepi.o
    @8
    epii.z
    isepi.y
    isepi.x
    oppcco
    eqeq12d
    wph
    cB
    @0
    @1
    cF
    cG
    @0
    chom
    cfv
    #
    cK
    @0
    cmon
    cfv
    #
    cY
    cX
    cZ
    cB
    cC
    @0
    @8
    isepi.b
    oppcbas
    @9
    eqid
    @1
    eqid
    @10
    eqid
    #
    wph
    cC
    ccat
    wcel
    @0
    ccat
    wcel
    isepi.c
    cC
    @0
    @8
    oppccat
    syl
    isepi.y
    isepi.x
    epii.z
    wph
    cF
    cX
    cY
    cE
    co
    cY
    cX
    @10
    co
    epii.f
    wph
    cC
    cE
    @10
    @0
    cY
    cX
    @8
    isepi.c
    @11
    isepi.e
    oppcmon
    eleqtrrd
    wph
    cG
    cY
    cZ
    cH
    co
    #
    cZ
    cY
    @9
    co
    #
    epii.g
    cC
    cH
    @0
    cZ
    cY
    isepi.h
    @8
    oppchom
    #
    syl6eleqr
    wph
    cK
    @12
    @13
    epii.k
    @14
    syl6eleqr
    moni
    bitr3d
end
