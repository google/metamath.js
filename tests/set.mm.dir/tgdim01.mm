include "wcel.mm"
include "cv.mm"
include "co.mm"
include "w3o.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "wb.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "istrkg2ld.mm"
include "syl.mm"
include "mtbid.mm"
include "rexnal2.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "con2bii.mm"
include "sylibr.mm"
include "w3a.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "eleq1.mm"
include "3orbi123d.mm"
include "oveq2.mm"
include "rspc3v.mm"
include "imp.mm"
include "syl31anc.mm"

theorem tgdim01
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tgdim01.p: |- P = ( Base ` G )
  assume tgdim01.i: |- I = ( Itv ` G )
  assume tgdim01.g: |- ( ph -> G e. V )
  assume tgdim01.1: |- ( ph -> -. G TarskiGDim>= 2 )
  assume tgdim01.x: |- ( ph -> X e. P )
  assume tgdim01.y: |- ( ph -> Y e. P )
  assume tgdim01.z: |- ( ph -> Z e. P )


  assert |- ( ph -> ( Z e. ( X I Y ) \/ X e. ( Z I Y ) \/ Y e. ( X I Z ) ) )

  proof
    wph
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    cZ
    cP
    wcel
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    co
    #
    wcel
    #
    @4
    @3
    @5
    cI
    co
    #
    wcel
    #
    @5
    @4
    @3
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cP
    wral
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    cZ
    cX
    cY
    cI
    co
    #
    wcel
    #
    cX
    cZ
    cY
    cI
    co
    #
    wcel
    #
    cY
    cX
    cZ
    cI
    co
    #
    wcel
    #
    w3o
    #
    tgdim01.x
    tgdim01.y
    tgdim01.z
    wph
    @12
    wn
    vz
    cP
    wrex
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    wn
    @14
    wph
    cG
    c2
    cstrkgld
    wbr
    #
    @23
    tgdim01.1
    wph
    cG
    cV
    wcel
    @24
    @23
    wb
    tgdim01.g
    vx
    vy
    vz
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cV
    tgdim01.p
    @25
    eqid
    tgdim01.i
    istrkg2ld
    syl
    mtbid
    @23
    @14
    @23
    @13
    wn
    #
    vx
    cP
    wrex
    @14
    wn
    @22
    @26
    vx
    cP
    @12
    vy
    vz
    cP
    cP
    rexnal2
    rexbii
    @13
    vx
    cP
    rexnal
    bitri
    con2bii
    sylibr
    @0
    @1
    @2
    w3a
    @14
    @21
    @12
    @21
    @3
    cX
    @5
    cI
    co
    #
    wcel
    #
    cX
    @8
    wcel
    #
    @5
    cX
    @3
    cI
    co
    #
    wcel
    #
    w3o
    @3
    @15
    wcel
    #
    cX
    @3
    cY
    cI
    co
    #
    wcel
    #
    cY
    @30
    wcel
    #
    w3o
    vx
    vy
    vz
    cX
    cY
    cZ
    cP
    cP
    cP
    @4
    cX
    wceq
    #
    @7
    @28
    @9
    @29
    @11
    @31
    @36
    @6
    @27
    @3
    @4
    cX
    @5
    cI
    oveq1
    eleq2d
    @4
    cX
    @8
    eleq1
    @36
    @10
    @30
    @5
    @4
    cX
    @3
    cI
    oveq1
    eleq2d
    3orbi123d
    @5
    cY
    wceq
    #
    @28
    @32
    @29
    @34
    @31
    @35
    @37
    @27
    @15
    @3
    @5
    cY
    cX
    cI
    oveq2
    eleq2d
    @37
    @8
    @33
    cX
    @5
    cY
    @3
    cI
    oveq2
    eleq2d
    @5
    cY
    @30
    eleq1
    3orbi123d
    @3
    cZ
    wceq
    #
    @32
    @16
    @34
    @18
    @35
    @20
    @3
    cZ
    @15
    eleq1
    @38
    @33
    @17
    cX
    @3
    cZ
    cY
    cI
    oveq1
    eleq2d
    @38
    @30
    @19
    cY
    @3
    cZ
    cX
    cI
    oveq2
    eleq2d
    3orbi123d
    rspc3v
    imp
    syl31anc
end
