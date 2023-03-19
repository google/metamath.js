include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "ctrlson.mm"
include "cpths.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "1wlkd.mm"
include "wcel.mm"
include "cs2.mm"
include "fveq1i.mm"
include "s2fv0.mm"
include "syl5eq.mm"
include "syl.mm"
include "c1.mm"
include "cs1.mm"
include "fveq2i.mm"
include "s1len.mm"
include "eqtri.mm"
include "fveq12i.mm"
include "s2fv1.mm"
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "wlkv.mm"
include "3simpc.mm"
include "3syl.mm"
include "jca31.mm"
include "iswlkon.mm"
include "mpbir3and.mm"
include "1trld.mm"
include "istrlson.mm"
include "mpbir2and.mm"
include "1pthd.mm"
include "wi.mm"
include "adantl.mm"
include "simpl.mm"
include "ex.mm"
include "mpcom.mm"
include "ispthson.mm"

theorem 1pthond
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )
  assume 1wlkd.v: |- V = ( Vtx ` G )
  assume 1wlkd.i: |- I = ( iEdg ` G )


  assert |- ( ph -> F ( X ( PathsOn ` G ) Y ) P )

  proof
    wph
    cF
    cP
    cX
    cY
    cG
    cpthson
    cfv
    co
    wbr
    #
    cF
    cP
    cX
    cY
    cG
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cpths
    cfv
    wbr
    #
    wph
    @1
    cF
    cP
    cX
    cY
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    wph
    @3
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cX
    wceq
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    cY
    wceq
    #
    wph
    cP
    cF
    cG
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkd.v
    1wlkd.i
    1wlkd
    #
    wph
    cX
    cV
    wcel
    #
    @7
    1wlkd.x
    @12
    @6
    cc0
    cX
    cY
    cs2
    #
    cfv
    cX
    cc0
    cP
    @13
    1wlkd.p
    fveq1i
    cX
    cY
    cV
    s2fv0
    syl5eq
    syl
    wph
    @9
    c1
    @13
    cfv
    #
    cY
    @8
    c1
    cP
    @13
    1wlkd.p
    @8
    cJ
    cs1
    #
    chash
    cfv
    c1
    cF
    @15
    chash
    1wlkd.f
    fveq2i
    cJ
    s1len
    eqtri
    fveq12i
    wph
    cY
    cV
    wcel
    #
    @14
    cY
    wceq
    1wlkd.y
    cX
    cY
    cV
    s2fv1
    syl
    syl5eq
    wph
    @12
    @16
    wa
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @3
    @5
    @7
    @10
    w3a
    wb
    wph
    @12
    @16
    @19
    1wlkd.x
    1wlkd.y
    wph
    @5
    cG
    cvv
    wcel
    #
    @17
    @18
    w3a
    #
    @19
    @11
    cP
    cF
    cG
    wlkv
    #
    @21
    @17
    @18
    3simpc
    #
    3syl
    jca31
    #
    cX
    cY
    cP
    cvv
    cF
    cG
    cV
    cvv
    1wlkd.v
    iswlkon
    syl
    mpbir3and
    wph
    cP
    cF
    cG
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkd.v
    1wlkd.i
    1trld
    wph
    @20
    @1
    @3
    @4
    wa
    wb
    @25
    cX
    cY
    cP
    cvv
    cF
    cG
    cV
    cvv
    1wlkd.v
    istrlson
    syl
    mpbir2and
    wph
    cP
    cF
    cG
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkd.v
    1wlkd.i
    1pthd
    wph
    @20
    @0
    @1
    @2
    wa
    wb
    @5
    wph
    @20
    @11
    @5
    @22
    @19
    wph
    @20
    wi
    @23
    @24
    @19
    wph
    @20
    @19
    wph
    wa
    @12
    @16
    @19
    wph
    @12
    @19
    1wlkd.x
    adantl
    wph
    @16
    @19
    1wlkd.y
    adantl
    @19
    wph
    simpl
    jca31
    ex
    3syl
    mpcom
    cX
    cY
    cP
    cvv
    cF
    cG
    cV
    cvv
    1wlkd.v
    ispthson
    syl
    mpbir2and
end
