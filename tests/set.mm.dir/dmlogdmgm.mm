include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "wcel.mm"
include "cneg.mm"
include "cn0.mm"
include "wn.mm"
include "cz.mm"
include "cn.mm"
include "eldifi.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "simpr.mm"
include "nn0ge0d.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "adantr.mm"
include "nn0red.mm"
include "negrebd.mm"
include "wi.mm"
include "eqid.mm"
include "ellogdm.mm"
include "simprbi.mm"
include "imp.mm"
include "syldan.mm"
include "rpgt0d.mm"
include "lt0neg2d.mm"
include "mpbid.mm"
include "0red.mm"
include "ltnled.mm"
include "pm2.65da.mm"
include "eldmgm.mm"
include "sylanbrc.mm"

theorem dmlogdmgm
  let cA: class A


  assert |- ( A e. ( CC \ ( -oo (,] 0 ) ) -> A e. ( CC \ ( ZZ \ NN ) ) )

  proof
    cA
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    cn0
    wcel
    #
    wn
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    cA
    cc
    @0
    eldifi
    #
    @2
    @5
    cc0
    @4
    cle
    wbr
    #
    @2
    @5
    wa
    #
    @4
    @2
    @5
    simpr
    #
    nn0ge0d
    @8
    @4
    cc0
    clt
    wbr
    #
    @7
    wn
    @8
    cc0
    cA
    clt
    wbr
    @10
    @8
    cA
    @2
    @5
    cA
    cr
    wcel
    #
    cA
    crp
    wcel
    #
    @8
    cA
    @2
    @3
    @5
    @6
    adantr
    @8
    @4
    @9
    nn0red
    #
    negrebd
    #
    @2
    @11
    @12
    @2
    @3
    @11
    @12
    wi
    cA
    @1
    @1
    eqid
    ellogdm
    simprbi
    imp
    syldan
    rpgt0d
    @8
    cA
    @14
    lt0neg2d
    mpbid
    @8
    @4
    cc0
    @13
    @8
    0red
    ltnled
    mpbid
    pm2.65da
    cA
    eldmgm
    sylanbrc
end
