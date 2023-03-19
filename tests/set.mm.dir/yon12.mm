include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "co.mm"
include "ccid.mm"
include "cop.mm"
include "coppc.mm"
include "chof.mm"
include "cco.mm"
include "ccurf.mm"
include "eqid.mm"
include "yonval.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "oveqd.mm"
include "chomf.mm"
include "crn.mm"
include "csetc.mm"
include "chom.mm"
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
include "oppchom.mm"
include "syl6eleqr.mm"
include "curf12.mm"
include "eqtrd.mm"
include "catidcl.mm"
include "hof2.mm"
include "oppcco.mm"
include "oveq1d.mm"
include "catcocl.mm"
include "catlid.mm"
include "3eqtrd.mm"

theorem yon12
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume yon11.y: |- Y = ( Yon ` C )
  assume yon11.b: |- B = ( Base ` C )
  assume yon11.c: |- ( ph -> C e. Cat )
  assume yon11.p: |- ( ph -> X e. B )
  assume yon11.h: |- H = ( Hom ` C )
  assume yon11.z: |- ( ph -> Z e. B )
  assume yon12.x: |- .x. = ( comp ` C )
  assume yon12.w: |- ( ph -> W e. B )
  assume yon12.f: |- ( ph -> F e. ( W H Z ) )
  assume yon12.g: |- ( ph -> G e. ( Z H X ) )


  assert |- ( ph -> ( ( ( Z ( 2nd ` ( ( 1st ` Y ) ` X ) ) W ) ` F ) ` G ) = ( G ( <. W , Z >. .x. X ) F ) )

  proof
    wph
    cG
    cF
    cZ
    cW
    cX
    cY
    c1st
    cfv
    #
    cfv
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    cG
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    cF
    cX
    cZ
    cop
    #
    cX
    cW
    cop
    cC
    coppc
    cfv
    #
    chof
    cfv
    #
    c2nd
    cfv
    co
    co
    #
    cfv
    cF
    cG
    @7
    cW
    @8
    cco
    cfv
    #
    co
    co
    #
    @6
    cX
    cX
    cop
    cW
    @11
    co
    #
    co
    #
    cG
    cF
    cW
    cZ
    cop
    cX
    c.x
    co
    co
    #
    wph
    cG
    @4
    @10
    wph
    @4
    cF
    cZ
    cW
    cX
    cC
    @8
    cop
    @9
    ccurf
    co
    #
    c1st
    cfv
    #
    cfv
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    @10
    wph
    cF
    @3
    @20
    wph
    @2
    @19
    cZ
    cW
    wph
    @1
    @18
    c2nd
    wph
    cX
    @0
    @17
    wph
    cY
    @16
    c1st
    wph
    cC
    @9
    @8
    cY
    yon11.y
    yon11.c
    @8
    eqid
    #
    @9
    eqid
    #
    yonval
    fveq2d
    fveq1d
    fveq2d
    oveqd
    fveq1d
    wph
    cB
    cB
    cC
    @8
    @5
    cC
    chomf
    cfv
    #
    crn
    #
    csetc
    cfv
    #
    @9
    @16
    cF
    @8
    chom
    cfv
    #
    @18
    cX
    cZ
    cW
    @16
    eqid
    yon11.b
    yon11.c
    wph
    cC
    ccat
    wcel
    @8
    ccat
    wcel
    yon11.c
    cC
    @8
    @21
    oppccat
    syl
    #
    wph
    cC
    @25
    @24
    @9
    @8
    cvv
    @21
    @22
    @25
    eqid
    yon11.c
    @24
    cvv
    wcel
    wph
    @23
    cC
    chomf
    fvex
    rnex
    a1i
    @24
    @24
    wss
    wph
    @24
    ssid
    a1i
    oppchofcl
    cB
    cC
    @8
    @21
    yon11.b
    oppcbas
    #
    yon11.p
    @18
    eqid
    yon11.z
    @26
    eqid
    #
    @5
    eqid
    #
    yon12.w
    wph
    cF
    cW
    cZ
    cH
    co
    cZ
    cW
    @26
    co
    yon12.f
    cC
    cH
    @8
    cZ
    cW
    yon11.h
    @21
    oppchom
    syl6eleqr
    #
    curf12
    eqtrd
    fveq1d
    wph
    cB
    @8
    @11
    @6
    cF
    @26
    cG
    @9
    cW
    cX
    cZ
    cX
    @22
    @27
    @28
    @29
    yon11.p
    yon11.z
    yon11.p
    yon12.w
    @11
    eqid
    wph
    @6
    cX
    cX
    cH
    co
    cX
    cX
    @26
    co
    wph
    cB
    cC
    @5
    cH
    cX
    yon11.b
    yon11.h
    @30
    yon11.c
    yon11.p
    catidcl
    cC
    cH
    @8
    cX
    cX
    yon11.h
    @21
    oppchom
    syl6eleqr
    @31
    wph
    cG
    cZ
    cX
    cH
    co
    cX
    cZ
    @26
    co
    yon12.g
    cC
    cH
    @8
    cX
    cZ
    yon11.h
    @21
    oppchom
    syl6eleqr
    hof2
    wph
    @14
    @15
    @6
    @13
    co
    @6
    @15
    cW
    cX
    cop
    cX
    c.x
    co
    co
    @15
    wph
    @12
    @15
    @6
    @13
    wph
    cB
    cC
    c.x
    cG
    cF
    @8
    cX
    cZ
    cW
    yon11.b
    yon12.x
    @21
    yon11.p
    yon11.z
    yon12.w
    oppcco
    oveq1d
    wph
    cB
    cC
    c.x
    @6
    @15
    @8
    cX
    cX
    cW
    yon11.b
    yon12.x
    @21
    yon11.p
    yon11.p
    yon12.w
    oppcco
    wph
    cB
    cC
    c.x
    @5
    @15
    cH
    cW
    cX
    yon11.b
    yon11.h
    @30
    yon11.c
    yon12.w
    yon12.x
    yon11.p
    wph
    cB
    cC
    c.x
    cF
    cG
    cH
    cW
    cZ
    cX
    yon11.b
    yon11.h
    yon12.x
    yon11.c
    yon12.w
    yon11.z
    yon11.p
    yon12.f
    yon12.g
    catcocl
    catlid
    3eqtrd
    3eqtrd
end
