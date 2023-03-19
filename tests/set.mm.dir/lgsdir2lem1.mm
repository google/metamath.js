include "c1.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cneg.mm"
include "c7.mm"
include "wa.mm"
include "c3.mm"
include "c5.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "1re.mm"
include "8re.mm"
include "8pos.mm"
include "elrpii.mm"
include "0le1.mm"
include "1lt8.mm"
include "modid.mm"
include "mp4an.mm"
include "cmul.mm"
include "caddc.mm"
include "8cn.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "ax-1cn.mm"
include "negcli.mm"
include "cmin.mm"
include "negsubi.mm"
include "7cn.mm"
include "addcomi.mm"
include "df-8.mm"
include "eqtr4i.mm"
include "subaddrii.mm"
include "eqtri.mm"
include "addcomli.mm"
include "oveq1i.mm"
include "cz.mm"
include "renegcli.mm"
include "1z.mm"
include "modcyc.mm"
include "mp3an.mm"
include "7re.mm"
include "0re.mm"
include "7pos.mm"
include "ltleii.mm"
include "7lt8.mm"
include "3eqtr3i.mm"
include "pm3.2i.mm"
include "3re.mm"
include "3pos.mm"
include "3lt8.mm"
include "3cn.mm"
include "5cn.mm"
include "5p3e8.mm"
include "5re.mm"
include "5pos.mm"
include "5lt8.mm"

theorem lgsdir2lem1
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p
  let cA: class A
  let cN: class N


  assert |- ( ( ( 1 mod 8 ) = 1 /\ ( -u 1 mod 8 ) = 7 ) /\ ( ( 3 mod 8 ) = 3 /\ ( -u 3 mod 8 ) = 5 ) )

  proof
    c1
    c8
    cmo
    co
    c1
    wceq
    #
    c1
    cneg
    #
    c8
    cmo
    co
    #
    c7
    wceq
    #
    wa
    c3
    c8
    cmo
    co
    c3
    wceq
    #
    c3
    cneg
    #
    c8
    cmo
    co
    #
    c5
    wceq
    #
    wa
    @0
    @3
    c1
    cr
    wcel
    c8
    crp
    wcel
    #
    cc0
    c1
    cle
    wbr
    c1
    c8
    clt
    wbr
    @0
    1re
    c8
    8re
    8pos
    elrpii
    #
    0le1
    1lt8
    c1
    c8
    modid
    mp4an
    @1
    c1
    c8
    cmul
    co
    #
    caddc
    co
    #
    c8
    cmo
    co
    #
    c7
    c8
    cmo
    co
    #
    @2
    c7
    @11
    c7
    c8
    cmo
    @11
    @1
    c8
    caddc
    co
    c7
    @10
    c8
    @1
    caddc
    c8
    8cn
    mulid2i
    #
    oveq2i
    c8
    @1
    c7
    8cn
    c1
    ax-1cn
    negcli
    c8
    @1
    caddc
    co
    c8
    c1
    cmin
    co
    c7
    c8
    c1
    8cn
    ax-1cn
    negsubi
    c8
    c1
    c7
    8cn
    ax-1cn
    7cn
    c1
    c7
    caddc
    co
    c7
    c1
    caddc
    co
    c8
    c1
    c7
    ax-1cn
    7cn
    addcomi
    df-8
    eqtr4i
    subaddrii
    eqtri
    addcomli
    eqtri
    oveq1i
    @1
    cr
    wcel
    @8
    c1
    cz
    wcel
    #
    @12
    @2
    wceq
    c1
    1re
    renegcli
    @9
    1z
    @1
    c8
    c1
    modcyc
    mp3an
    c7
    cr
    wcel
    @8
    cc0
    c7
    cle
    wbr
    c7
    c8
    clt
    wbr
    @13
    c7
    wceq
    7re
    @9
    cc0
    c7
    0re
    7re
    7pos
    ltleii
    7lt8
    c7
    c8
    modid
    mp4an
    3eqtr3i
    pm3.2i
    @4
    @7
    c3
    cr
    wcel
    @8
    cc0
    c3
    cle
    wbr
    c3
    c8
    clt
    wbr
    @4
    3re
    @9
    cc0
    c3
    0re
    3re
    3pos
    ltleii
    3lt8
    c3
    c8
    modid
    mp4an
    @5
    @10
    caddc
    co
    #
    c8
    cmo
    co
    #
    c5
    c8
    cmo
    co
    #
    @6
    c5
    @16
    c5
    c8
    cmo
    @16
    @5
    c8
    caddc
    co
    c5
    @10
    c8
    @5
    caddc
    @14
    oveq2i
    c8
    @5
    c5
    8cn
    c3
    3cn
    negcli
    c8
    @5
    caddc
    co
    c8
    c3
    cmin
    co
    c5
    c8
    c3
    8cn
    3cn
    negsubi
    c8
    c3
    c5
    8cn
    3cn
    5cn
    c5
    c3
    c8
    5cn
    3cn
    5p3e8
    addcomli
    subaddrii
    eqtri
    addcomli
    eqtri
    oveq1i
    @5
    cr
    wcel
    @8
    @15
    @17
    @6
    wceq
    c3
    3re
    renegcli
    @9
    1z
    @5
    c8
    c1
    modcyc
    mp3an
    c5
    cr
    wcel
    @8
    cc0
    c5
    cle
    wbr
    c5
    c8
    clt
    wbr
    @18
    c5
    wceq
    5re
    @9
    cc0
    c5
    0re
    5re
    5pos
    ltleii
    5lt8
    c5
    c8
    modid
    mp4an
    3eqtr3i
    pm3.2i
    pm3.2i
end
