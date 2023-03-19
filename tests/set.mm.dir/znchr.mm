include "cn0.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "czrh.mm"
include "c0g.mm"
include "crg.mm"
include "cz.mm"
include "ccrg.mm"
include "zncrng.mm"
include "crngring.mm"
include "syl.mm"
include "nn0z.mm"
include "eqid.mm"
include "chrdvds.mm"
include "syl2an.mm"
include "zndvds0.mm"
include "sylan2.mm"
include "bitrd.mm"
include "ralrimiva.mm"
include "chrcl.mm"
include "dvdsext.mm"
include "mpancom.mm"
include "mpbird.mm"

theorem znchr
  let cN: class N
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cE: class E
  let cL: class L
  let cU: class U
  assume znchr.y: |- Y = ( Z/nZ ` N )


  assert |- ( N e. NN0 -> ( chr ` Y ) = N )

  proof
    cN
    cn0
    wcel
    #
    cY
    cchr
    cfv
    #
    cN
    wceq
    #
    @1
    vx
    cv
    #
    cdvds
    wbr
    #
    cN
    @3
    cdvds
    wbr
    #
    wb
    #
    vx
    cn0
    wral
    #
    @0
    @6
    vx
    cn0
    @0
    @3
    cn0
    wcel
    #
    wa
    @4
    @3
    cY
    czrh
    cfv
    #
    cfv
    cY
    c0g
    cfv
    #
    wceq
    #
    @5
    @0
    cY
    crg
    wcel
    #
    @3
    cz
    wcel
    #
    @4
    @11
    wb
    @8
    @0
    cY
    ccrg
    wcel
    @12
    cN
    cY
    znchr.y
    zncrng
    cY
    crngring
    syl
    #
    @3
    nn0z
    #
    @1
    cY
    @9
    @3
    @10
    @1
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    chrdvds
    syl2an
    @8
    @0
    @13
    @11
    @5
    wb
    @15
    @3
    @9
    cN
    cY
    @10
    znchr.y
    @17
    @18
    zndvds0
    sylan2
    bitrd
    ralrimiva
    @1
    cn0
    wcel
    #
    @0
    @2
    @7
    wb
    @0
    @12
    @19
    @14
    @1
    cY
    @16
    chrcl
    syl
    vx
    @1
    cN
    dvdsext
    mpancom
    mpbird
end
