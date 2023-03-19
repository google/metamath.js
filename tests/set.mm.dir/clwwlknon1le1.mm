include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cclwwlknon.mm"
include "co.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "csn.mm"
include "cedg.mm"
include "wa.mm"
include "cs1.mm"
include "wceq.mm"
include "eqid.mm"
include "clwwlknon1loop.mm"
include "fveq2.mm"
include "cvv.mm"
include "cword.mm"
include "s1cli.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "syl.mm"
include "wnel.mm"
include "c0.mm"
include "clwwlknon1nloop.mm"
include "adantl.mm"
include "cc0.mm"
include "hash0.mm"
include "0le1.mm"
include "pm2.61danel.mm"
include "wn.mm"
include "cn.mm"
include "id.mm"
include "intnanrd.mm"
include "clwwlknon0.mm"
include "fveq2d.mm"
include "pm2.61i.mm"

theorem clwwlknon1le1
  let cG: class G
  let cX: class X


  assert |- ( # ` ( X ( ClWWalksNOn ` G ) 1 ) ) <_ 1

  proof
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    cX
    c1
    cG
    cclwwlknon
    cfv
    #
    co
    #
    chash
    cfv
    #
    c1
    cle
    wbr
    #
    @1
    @5
    cX
    csn
    #
    cG
    cedg
    cfv
    #
    @1
    @6
    @7
    wcel
    wa
    @3
    cX
    cs1
    #
    csn
    #
    wceq
    #
    @5
    @2
    @7
    cG
    @0
    cX
    @0
    eqid
    #
    @2
    eqid
    #
    @7
    eqid
    #
    clwwlknon1loop
    @10
    @4
    c1
    c1
    cle
    @10
    @4
    @9
    chash
    cfv
    #
    c1
    @3
    @9
    chash
    fveq2
    @8
    cvv
    cword
    #
    wcel
    @14
    c1
    wceq
    cX
    s1cli
    @8
    @15
    hashsng
    ax-mp
    syl6eq
    1le1
    syl6eqbr
    syl
    @1
    @6
    @7
    wnel
    #
    wa
    @3
    c0
    wceq
    #
    @5
    @16
    @17
    @1
    @2
    @7
    cG
    @0
    cX
    @11
    @12
    @13
    clwwlknon1nloop
    adantl
    @17
    @4
    cc0
    c1
    cle
    @17
    @4
    c0
    chash
    cfv
    #
    cc0
    @3
    c0
    chash
    fveq2
    hash0
    syl6eq
    0le1
    syl6eqbr
    syl
    pm2.61danel
    @1
    wn
    #
    @4
    cc0
    c1
    cle
    @19
    @4
    @18
    cc0
    @19
    @3
    c0
    chash
    @19
    @1
    c1
    cn
    wcel
    #
    wa
    wn
    @17
    @19
    @1
    @20
    @19
    id
    intnanrd
    cG
    c1
    cX
    clwwlknon0
    syl
    fveq2d
    hash0
    syl6eq
    0le1
    syl6eqbr
    pm2.61i
end
