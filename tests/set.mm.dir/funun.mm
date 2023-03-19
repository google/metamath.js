include "wfun.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "funrel.mm"
include "anim12i.mm"
include "relun.mm"
include "sylibr.mm"
include "adantr.mm"
include "wo.mm"
include "elun.mm"
include "anbi12i.mm"
include "anddi.mm"
include "bitri.mm"
include "wn.mm"
include "disj1.mm"
include "biimpi.mm"
include "19.21bi.mm"
include "imnan.mm"
include "sylib.mm"
include "vex.mm"
include "opeldm.mm"
include "nsyl.mm"
include "orel2.mm"
include "syl.mm"
include "con2d.mm"
include "orel1.mm"
include "orim12d.mm"
include "adantl.mm"
include "syl5bi.mm"
include "dffun4.mm"
include "simprbi.mm"
include "19.21bbi.mm"
include "jaao.mm"
include "syld.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "sylanbrc.mm"

theorem funun
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( Fun F /\ Fun G ) /\ ( dom F i^i dom G ) = (/) ) -> Fun ( F u. G ) )

  proof
    cF
    wfun
    #
    cG
    wfun
    #
    wa
    #
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    c0
    wceq
    #
    wa
    #
    cF
    cG
    cun
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @7
    wcel
    #
    @9
    vz
    cv
    #
    cop
    #
    @7
    wcel
    #
    wa
    #
    @10
    @13
    wceq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @7
    wfun
    @2
    @8
    @5
    @2
    cF
    wrel
    #
    cG
    wrel
    #
    wa
    @8
    @0
    @20
    @1
    @21
    cF
    funrel
    cG
    funrel
    anim12i
    cF
    cG
    relun
    sylibr
    adantr
    @6
    @19
    vx
    vy
    @6
    @18
    vz
    @6
    @16
    @11
    cF
    wcel
    #
    @14
    cF
    wcel
    #
    wa
    #
    @11
    cG
    wcel
    #
    @14
    cG
    wcel
    #
    wa
    #
    wo
    #
    @17
    @16
    @24
    @22
    @26
    wa
    #
    wo
    #
    @25
    @23
    wa
    #
    @27
    wo
    #
    wo
    #
    @6
    @28
    @16
    @22
    @25
    wo
    #
    @23
    @26
    wo
    #
    wa
    @33
    @12
    @34
    @15
    @35
    @11
    cF
    cG
    elun
    @14
    cF
    cG
    elun
    anbi12i
    @22
    @25
    @23
    @26
    anddi
    bitri
    @5
    @33
    @28
    wi
    @2
    @5
    @30
    @24
    @32
    @27
    @5
    @29
    wn
    @30
    @24
    wi
    @5
    @9
    @3
    wcel
    #
    @9
    @4
    wcel
    #
    wa
    #
    @29
    @5
    @36
    @37
    wn
    wi
    #
    @38
    wn
    @5
    @39
    vx
    @5
    @39
    vx
    wal
    vx
    @3
    @4
    disj1
    biimpi
    19.21bi
    #
    @36
    @37
    imnan
    sylib
    @22
    @36
    @26
    @37
    @9
    @10
    cF
    vx
    vex
    #
    vy
    vex
    #
    opeldm
    @9
    @13
    cG
    @41
    vz
    vex
    #
    opeldm
    anim12i
    nsyl
    @29
    @24
    orel2
    syl
    @5
    @31
    wn
    @32
    @27
    wi
    @5
    @37
    @36
    wa
    #
    @31
    @5
    @37
    @36
    wn
    wi
    @44
    wn
    @5
    @36
    @37
    @40
    con2d
    @37
    @36
    imnan
    sylib
    @25
    @37
    @23
    @36
    @9
    @10
    cG
    @41
    @42
    opeldm
    @9
    @13
    cF
    @41
    @43
    opeldm
    anim12i
    nsyl
    @31
    @27
    orel1
    syl
    orim12d
    adantl
    syl5bi
    @2
    @28
    @17
    wi
    @5
    @0
    @24
    @17
    @1
    @27
    @0
    @24
    @17
    wi
    #
    vy
    vz
    @0
    @45
    vz
    wal
    vy
    wal
    #
    vx
    @0
    @20
    @46
    vx
    wal
    vx
    vy
    vz
    cF
    dffun4
    simprbi
    19.21bi
    19.21bbi
    @1
    @27
    @17
    wi
    #
    vy
    vz
    @1
    @47
    vz
    wal
    vy
    wal
    #
    vx
    @1
    @21
    @48
    vx
    wal
    vx
    vy
    vz
    cG
    dffun4
    simprbi
    19.21bi
    19.21bbi
    jaao
    adantr
    syld
    alrimiv
    alrimivv
    vx
    vy
    vz
    @7
    dffun4
    sylanbrc
end
