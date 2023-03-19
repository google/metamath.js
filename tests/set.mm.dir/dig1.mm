include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cdig.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "cexp.mm"
include "eluzelcn.mm"
include "exp0d.mm"
include "eqcomd.mm"
include "ad2antrl.mm"
include "oveq2d.mm"
include "cn0.mm"
include "simprl.mm"
include "simpr.mm"
include "anim2i.mm"
include "ancomd.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "0nn0.mm"
include "a1i.mm"
include "digexp.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "wn.mm"
include "cn.mm"
include "cdif.mm"
include "eluz2nn.mm"
include "simprr.mm"
include "wi.mm"
include "nn0ge0.mm"
include "con3d.mm"
include "impcom.mm"
include "eldifd.mm"
include "1nn0.mm"
include "dignn0fr.mm"
include "0le0.mm"
include "breq2.mm"
include "mpbiri.mm"
include "iffalsed.mm"
include "eqtr4d.mm"
include "pm2.61ian.mm"

theorem dig1
  let cB: class B
  let cK: class K
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ K e. ZZ ) -> ( K ( digit ` B ) 1 ) = if ( K = 0 , 1 , 0 ) )

  proof
    cc0
    cK
    cle
    wbr
    #
    cB
    c2
    cuz
    cfv
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    c1
    cB
    cdig
    cfv
    #
    co
    #
    cK
    cc0
    wceq
    #
    c1
    cc0
    cif
    #
    wceq
    @0
    @3
    wa
    #
    @5
    cK
    cB
    cc0
    cexp
    co
    #
    @4
    co
    #
    @7
    @8
    c1
    @9
    cK
    @4
    @1
    c1
    @9
    wceq
    @0
    @2
    @1
    @9
    c1
    @1
    cB
    c2
    cB
    eluzelcn
    exp0d
    eqcomd
    ad2antrl
    oveq2d
    @8
    @1
    cK
    cn0
    wcel
    #
    cc0
    cn0
    wcel
    #
    @10
    @7
    wceq
    @0
    @1
    @2
    simprl
    @8
    @2
    @0
    wa
    @11
    @8
    @0
    @2
    @3
    @2
    @0
    @1
    @2
    simpr
    anim2i
    ancomd
    cK
    elnn0z
    sylibr
    @12
    @8
    0nn0
    a1i
    cB
    cK
    cc0
    digexp
    syl3anc
    eqtrd
    @0
    wn
    #
    @3
    wa
    #
    @5
    cc0
    @7
    @14
    cB
    cn
    wcel
    #
    cK
    cz
    cn0
    cdif
    wcel
    c1
    cn0
    wcel
    #
    @5
    cc0
    wceq
    @1
    @15
    @13
    @2
    cB
    eluz2nn
    ad2antrl
    @14
    cK
    cz
    cn0
    @13
    @1
    @2
    simprr
    @3
    @13
    @11
    wn
    @3
    @11
    @0
    @11
    @0
    wi
    @3
    cK
    nn0ge0
    a1i
    con3d
    impcom
    eldifd
    @16
    @14
    1nn0
    a1i
    cB
    cK
    c1
    dignn0fr
    syl3anc
    @14
    @6
    c1
    cc0
    @3
    @13
    @6
    wn
    @3
    @6
    @0
    @6
    @0
    wi
    @3
    @6
    @0
    cc0
    cc0
    cle
    wbr
    0le0
    cK
    cc0
    cc0
    cle
    breq2
    mpbiri
    a1i
    con3d
    impcom
    iffalsed
    eqtr4d
    pm2.61ian
end
