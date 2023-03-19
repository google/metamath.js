include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cen.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0g.mm"
include "cfv.mm"
include "cbs.mm"
include "cvv.mm"
include "wceq.mm"
include "c2.mm"
include "czn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "frlmbas.mm"
include "mpan.mm"
include "syl6eqr.mm"
include "enrefg.mm"
include "chash.mm"
include "cn.mm"
include "2nn.mm"
include "znhash.mm"
include "ax-mp.mm"
include "hash2.mm"
include "eqtr4i.mm"
include "wb.mm"
include "cn0.mm"
include "2nn0.mm"
include "hashclb.mm"
include "mpbir.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "hashen.mm"
include "mp2an.mm"
include "mpbi.mm"
include "a1i.mm"
include "crg.mm"
include "ccrg.mm"
include "zncrng.mm"
include "crngring.mm"
include "mp2b.mm"
include "ring0cl.mm"
include "mp1i.mm"
include "wne.mm"
include "2on0.mm"
include "con0.mm"
include "2on.mm"
include "on0eln0.mm"
include "mapfien2.mm"
include "eqbrtrrd.mm"
include "pwfi2en.mm"
include "entr.mm"
include "syl2anc.mm"

theorem frlmpwfi
  let cB: class B
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  let vx: setvar x
  assume frlmpwfi.r: |- R = ( Z/nZ ` 2 )
  assume frlmpwfi.y: |- Y = ( R freeLMod I )
  assume frlmpwfi.b: |- B = ( Base ` Y )


  assert |- ( I e. V -> B ~~ ( ~P I i^i Fin ) )

  proof
    cI
    cV
    wcel
    #
    cB
    vx
    cv
    #
    c0
    cfsupp
    wbr
    vx
    c2o
    cI
    cmap
    co
    crab
    #
    cen
    wbr
    @2
    cI
    cpw
    cfn
    cin
    #
    cen
    wbr
    cB
    @3
    cen
    wbr
    @0
    @1
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    vx
    cR
    cbs
    cfv
    #
    cI
    cmap
    co
    crab
    #
    cB
    @2
    cen
    @0
    @6
    cY
    cbs
    cfv
    #
    cB
    cR
    cvv
    wcel
    @0
    @6
    @7
    wceq
    cR
    c2
    czn
    cfv
    cvv
    frlmpwfi.r
    c2
    czn
    fvex
    eqeltri
    @6
    cR
    vx
    cY
    cI
    @5
    cvv
    cV
    @4
    frlmpwfi.y
    @5
    eqid
    #
    @4
    eqid
    #
    @6
    eqid
    #
    frlmbas
    mpan
    frlmpwfi.b
    syl6eqr
    @0
    vx
    cI
    @5
    cI
    c2o
    @6
    @2
    c0
    @4
    @10
    @2
    eqid
    #
    cI
    cV
    enrefg
    @5
    c2o
    cen
    wbr
    #
    @0
    @5
    chash
    cfv
    #
    c2o
    chash
    cfv
    #
    wceq
    #
    @12
    @13
    c2
    @14
    c2
    cn
    wcel
    @13
    c2
    wceq
    2nn
    @5
    c2
    cR
    frlmpwfi.r
    @8
    znhash
    ax-mp
    #
    hash2
    eqtr4i
    @5
    cfn
    wcel
    #
    c2o
    cfn
    wcel
    #
    @15
    @12
    wb
    @17
    @13
    cn0
    wcel
    #
    @13
    c2
    cn0
    @16
    2nn0
    eqeltri
    @5
    cvv
    wcel
    @17
    @19
    wb
    cR
    cbs
    fvex
    @5
    cvv
    hashclb
    ax-mp
    mpbir
    c2o
    com
    wcel
    @18
    2onn
    c2o
    nnfi
    ax-mp
    @5
    c2o
    hashen
    mp2an
    mpbi
    a1i
    cR
    crg
    wcel
    #
    @4
    @5
    wcel
    @0
    c2
    cn0
    wcel
    cR
    ccrg
    wcel
    @20
    2nn0
    c2
    cR
    frlmpwfi.r
    zncrng
    cR
    crngring
    mp2b
    @5
    cR
    @4
    @8
    @9
    ring0cl
    mp1i
    c0
    c2o
    wcel
    #
    @0
    @21
    c2o
    c0
    wne
    #
    2on0
    c2o
    con0
    wcel
    @21
    @22
    wb
    2on
    c2o
    on0eln0
    ax-mp
    mpbir
    a1i
    mapfien2
    eqbrtrrd
    vx
    cI
    @2
    cV
    @11
    pwfi2en
    cB
    @2
    @3
    entr
    syl2anc
end
