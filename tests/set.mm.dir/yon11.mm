include "c1st.mm"
include "cfv.mm"
include "coppc.mm"
include "cop.mm"
include "chof.mm"
include "ccurf.mm"
include "co.mm"
include "eqid.mm"
include "yonval.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "chomf.mm"
include "crn.mm"
include "csetc.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "cvv.mm"
include "fvex.mm"
include "rnex.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "oppchofcl.mm"
include "oppcbas.mm"
include "curf11.mm"
include "chom.mm"
include "hof1.mm"
include "oppchom.mm"
include "syl6eq.mm"
include "3eqtrd.mm"

theorem yon11
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume yon11.y: |- Y = ( Yon ` C )
  assume yon11.b: |- B = ( Base ` C )
  assume yon11.c: |- ( ph -> C e. Cat )
  assume yon11.p: |- ( ph -> X e. B )
  assume yon11.h: |- H = ( Hom ` C )
  assume yon11.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( ( 1st ` ( ( 1st ` Y ) ` X ) ) ` Z ) = ( Z H X ) )

  proof
    wph
    cZ
    cX
    cY
    c1st
    cfv
    #
    cfv
    #
    c1st
    cfv
    #
    cfv
    cZ
    cX
    cC
    cC
    coppc
    cfv
    #
    cop
    @3
    chof
    cfv
    #
    ccurf
    co
    #
    c1st
    cfv
    #
    cfv
    #
    c1st
    cfv
    #
    cfv
    cX
    cZ
    @4
    c1st
    cfv
    co
    #
    cZ
    cX
    cH
    co
    #
    wph
    cZ
    @2
    @8
    wph
    @1
    @7
    c1st
    wph
    cX
    @0
    @6
    wph
    cY
    @5
    c1st
    wph
    cC
    @4
    @3
    cY
    yon11.y
    yon11.c
    @3
    eqid
    #
    @4
    eqid
    #
    yonval
    fveq2d
    fveq1d
    fveq2d
    fveq1d
    wph
    cB
    cB
    cC
    @3
    cC
    chomf
    cfv
    #
    crn
    #
    csetc
    cfv
    #
    @4
    @5
    @7
    cX
    cZ
    @5
    eqid
    yon11.b
    yon11.c
    wph
    cC
    ccat
    wcel
    @3
    ccat
    wcel
    yon11.c
    cC
    @3
    @11
    oppccat
    syl
    #
    wph
    cC
    @15
    @14
    @4
    @3
    cvv
    @11
    @12
    @15
    eqid
    yon11.c
    @14
    cvv
    wcel
    wph
    @13
    cC
    chomf
    fvex
    rnex
    a1i
    @14
    @14
    wss
    wph
    @14
    ssid
    a1i
    oppchofcl
    cB
    cC
    @3
    @11
    yon11.b
    oppcbas
    #
    yon11.p
    @7
    eqid
    yon11.z
    curf11
    wph
    @9
    cX
    cZ
    @3
    chom
    cfv
    #
    co
    @10
    wph
    cB
    @3
    @18
    @4
    cX
    cZ
    @12
    @16
    @17
    @18
    eqid
    yon11.p
    yon11.z
    hof1
    cC
    cH
    @3
    cX
    cZ
    yon11.h
    @11
    oppchom
    syl6eq
    3eqtrd
end
