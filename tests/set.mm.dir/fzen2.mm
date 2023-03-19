include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "cen.mm"
include "wbr.mm"
include "ccnv.mm"
include "cz.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancr.mm"
include "fzen.mm"
include "syl3anc.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan3.mm"
include "sylancl.mm"
include "zcn.mm"
include "addsubass.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "breqtrd.mm"
include "cn0.mm"
include "peano2uz.mm"
include "uznn0sub.mm"
include "fzennn.mm"
include "3syl.mm"
include "entr.mm"

theorem fzen2
  let vx: setvar x
  let cG: class G
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume fzennn.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )


  assert |- ( N e. ( ZZ>= ` M ) -> ( M ... N ) ~~ ( `' G ` ( ( N + 1 ) - M ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    cfz
    co
    #
    c1
    cN
    c1
    caddc
    co
    #
    cM
    cmin
    co
    #
    cfz
    co
    #
    cen
    wbr
    @5
    @4
    cG
    ccnv
    cfv
    #
    cen
    wbr
    #
    @2
    @6
    cen
    wbr
    @1
    @2
    cM
    c1
    cM
    cmin
    co
    #
    caddc
    co
    #
    cN
    @8
    caddc
    co
    #
    cfz
    co
    #
    @5
    cen
    @1
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @2
    @11
    cen
    wbr
    cM
    cN
    eluzel2
    #
    cM
    cN
    eluzelz
    #
    @1
    c1
    cz
    wcel
    @12
    @14
    1z
    @15
    c1
    cM
    zsubcl
    sylancr
    @8
    cM
    cN
    fzen
    syl3anc
    @1
    @9
    c1
    @10
    @4
    cfz
    @1
    cM
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @9
    c1
    wceq
    @1
    cM
    @15
    zcnd
    ax-1cn
    cM
    c1
    pncan3
    sylancl
    @1
    @4
    @10
    @1
    @13
    @12
    @4
    @10
    wceq
    #
    @16
    @15
    @13
    cN
    cc
    wcel
    #
    @17
    @19
    @12
    cN
    zcn
    cM
    zcn
    @20
    @18
    @17
    @19
    ax-1cn
    cN
    c1
    cM
    addsubass
    mp3an2
    syl2an
    syl2anc
    eqcomd
    oveq12d
    breqtrd
    @1
    @3
    @0
    wcel
    @4
    cn0
    wcel
    @7
    cM
    cN
    peano2uz
    cM
    @3
    uznn0sub
    vx
    cG
    @4
    fzennn.1
    fzennn
    3syl
    @2
    @5
    @6
    entr
    syl2anc
end
