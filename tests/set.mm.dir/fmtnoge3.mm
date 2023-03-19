include "cn0.mm"
include "wcel.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c3.mm"
include "cuz.mm"
include "fmtno.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "3z.mm"
include "a1i.mm"
include "2nn0.mm"
include "id.mm"
include "nn0expcld.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nn0zd.mm"
include "cmin.mm"
include "3m1e2.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "cr.mm"
include "2re.mm"
include "1le2.mm"
include "expge1d.mm"
include "1zzd.mm"
include "clt.mm"
include "1lt2.mm"
include "leexp2d.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "syl5eqbr.mm"
include "3re.mm"
include "1red.mm"
include "nn0red.mm"
include "lesubaddd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eqeltrd.mm"

theorem fmtnoge3
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( FermatNo ` N ) e. ( ZZ>= ` 3 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cfmtno
    cfv
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    c3
    cuz
    cfv
    #
    cN
    fmtno
    @0
    c3
    cz
    wcel
    #
    @3
    cz
    wcel
    c3
    @3
    cle
    wbr
    #
    @3
    @4
    wcel
    @5
    @0
    3z
    a1i
    @0
    @3
    @0
    @2
    cn0
    wcel
    @3
    cn0
    wcel
    @0
    c2
    @1
    c2
    cn0
    wcel
    @0
    2nn0
    a1i
    #
    @0
    c2
    cN
    @7
    @0
    id
    #
    nn0expcld
    #
    nn0expcld
    #
    @2
    peano2nn0
    syl
    nn0zd
    @0
    c3
    c1
    cmin
    co
    #
    @2
    cle
    wbr
    @6
    @0
    @11
    c2
    @2
    cle
    3m1e2
    @0
    c2
    c2
    c1
    cexp
    co
    #
    @2
    cle
    c2
    cc
    wcel
    @12
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    @0
    c1
    @1
    cle
    wbr
    @12
    @2
    cle
    wbr
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    #
    @8
    c1
    c2
    cle
    wbr
    @0
    1le2
    a1i
    expge1d
    @0
    c2
    c1
    @1
    @13
    @0
    1zzd
    @0
    @1
    @9
    nn0zd
    c1
    c2
    clt
    wbr
    @0
    1lt2
    a1i
    leexp2d
    mpbid
    syl5eqbrr
    syl5eqbr
    @0
    c3
    c1
    @2
    c3
    cr
    wcel
    @0
    3re
    a1i
    @0
    1red
    @0
    @2
    @10
    nn0red
    lesubaddd
    mpbid
    c3
    @3
    eluz2
    syl3anbrc
    eqeltrd
end
