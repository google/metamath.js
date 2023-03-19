include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "coppc.mm"
include "ccid.mm"
include "cop.mm"
include "chof.mm"
include "cco.mm"
include "ccurf.mm"
include "eqid.mm"
include "yonval.mm"
include "fveq2d.mm"
include "oveqd.mm"
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
include "curf2val.mm"
include "eqtrd.mm"
include "chom.mm"
include "oppchom.mm"
include "syl6eleqr.mm"
include "catidcl.mm"
include "hof2.mm"
include "catlid.mm"
include "oveq1d.mm"
include "oppcco.mm"
include "3eqtrd.mm"

theorem yon2
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
  assume yon2.f: |- ( ph -> F e. ( X H Z ) )
  assume yon2.g: |- ( ph -> G e. ( W H X ) )


  assert |- ( ph -> ( ( ( ( X ( 2nd ` Y ) Z ) ` F ) ` W ) ` G ) = ( F ( <. W , X >. .x. Z ) G ) )

  proof
    wph
    cG
    cW
    cF
    cX
    cZ
    cY
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    #
    cfv
    cG
    cF
    cW
    cC
    coppc
    cfv
    #
    ccid
    cfv
    #
    cfv
    #
    cX
    cW
    cop
    #
    cZ
    cW
    cop
    @4
    chof
    cfv
    #
    c2nd
    cfv
    co
    co
    #
    cfv
    @6
    cG
    @7
    cW
    @4
    cco
    cfv
    #
    co
    co
    #
    cF
    cZ
    cX
    cop
    cW
    @10
    co
    #
    co
    #
    cF
    cG
    cW
    cX
    cop
    cZ
    c.x
    co
    co
    #
    wph
    cG
    @3
    @9
    wph
    @3
    cW
    cF
    cX
    cZ
    cC
    @4
    cop
    @8
    ccurf
    co
    #
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    cfv
    @9
    wph
    cW
    @2
    @18
    wph
    cF
    @1
    @17
    wph
    @0
    @16
    cX
    cZ
    wph
    cY
    @15
    c2nd
    wph
    cC
    @8
    @4
    cY
    yon11.y
    yon11.c
    @4
    eqid
    #
    @8
    eqid
    #
    yonval
    fveq2d
    oveqd
    fveq1d
    fveq1d
    wph
    cB
    cB
    cC
    @4
    cC
    chomf
    cfv
    #
    crn
    #
    csetc
    cfv
    #
    @8
    @15
    cH
    @5
    cF
    @18
    cX
    cZ
    cW
    @15
    eqid
    yon11.b
    yon11.c
    wph
    cC
    ccat
    wcel
    @4
    ccat
    wcel
    yon11.c
    cC
    @4
    @19
    oppccat
    syl
    #
    wph
    cC
    @23
    @22
    @8
    @4
    cvv
    @19
    @20
    @23
    eqid
    yon11.c
    @22
    cvv
    wcel
    wph
    @21
    cC
    chomf
    fvex
    rnex
    a1i
    @22
    @22
    wss
    wph
    @22
    ssid
    a1i
    oppchofcl
    cB
    cC
    @4
    @19
    yon11.b
    oppcbas
    #
    yon11.h
    @5
    eqid
    #
    yon11.p
    yon11.z
    yon2.f
    @18
    eqid
    yon12.w
    curf2val
    eqtrd
    fveq1d
    wph
    cB
    @4
    @10
    cF
    @6
    @4
    chom
    cfv
    #
    cG
    @8
    cW
    cX
    cW
    cZ
    @20
    @24
    @25
    @27
    eqid
    #
    yon11.p
    yon12.w
    yon11.z
    yon12.w
    @10
    eqid
    #
    wph
    cF
    cX
    cZ
    cH
    co
    cZ
    cX
    @27
    co
    yon2.f
    cC
    cH
    @4
    cZ
    cX
    yon11.h
    @19
    oppchom
    syl6eleqr
    wph
    cB
    @4
    @5
    @27
    cW
    @25
    @28
    @26
    @24
    yon12.w
    catidcl
    wph
    cG
    cW
    cX
    cH
    co
    cX
    cW
    @27
    co
    yon2.g
    cC
    cH
    @4
    cX
    cW
    yon11.h
    @19
    oppchom
    syl6eleqr
    #
    hof2
    wph
    @13
    cG
    cF
    @12
    co
    @14
    wph
    @11
    cG
    cF
    @12
    wph
    cB
    @4
    @10
    @5
    cG
    @27
    cX
    cW
    @25
    @28
    @26
    @24
    yon11.p
    @29
    yon12.w
    @30
    catlid
    oveq1d
    wph
    cB
    cC
    c.x
    cF
    cG
    @4
    cZ
    cX
    cW
    yon11.b
    yon12.x
    @19
    yon11.z
    yon11.p
    yon12.w
    oppcco
    eqtrd
    3eqtrd
end
