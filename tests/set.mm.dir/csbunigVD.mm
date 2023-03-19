include "wcel.mm"
include "cuni.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wsbc.mm"
include "wb.mm"
include "wal.mm"
include "idn1.mm"
include "sbcg.mm"
include "e1a.mm"
include "sbcel2gOLD.mm"
include "pm4.38.mm"
include "ex.mm"
include "e11.mm"
include "sbcangOLD.mm"
include "bibi1.mm"
include "biimprcd.mm"
include "gen11.mm"
include "exbi.mm"
include "sbcexgOLD.mm"
include "abbi.mm"
include "biimpi.mm"
include "csbabgOLD.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "df-uni.mm"
include "ax-gen.mm"
include "spsbc.mm"
include "e10.mm"
include "sbceqg.mm"
include "in1.mm"

theorem csbunigVD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / x ]_ B )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cuni
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    cuni
    #
    wceq
    #
    @0
    @2
    vz
    cv
    vy
    cv
    #
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    wceq
    #
    @4
    @11
    wceq
    #
    @5
    @0
    vx
    cA
    @7
    @6
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    csb
    #
    @11
    wceq
    #
    @2
    @18
    wceq
    #
    @12
    @0
    @16
    vx
    cA
    wsbc
    #
    vz
    cab
    #
    @11
    wceq
    #
    @18
    @22
    wceq
    #
    @19
    @0
    @21
    @10
    wb
    #
    vz
    wal
    #
    @23
    @0
    @25
    vz
    @0
    @15
    vx
    cA
    wsbc
    #
    vy
    wex
    #
    @10
    wb
    #
    @21
    @28
    wb
    #
    @25
    @0
    @27
    @9
    wb
    #
    vy
    wal
    @29
    @0
    @31
    vy
    @0
    @7
    vx
    cA
    wsbc
    #
    @14
    vx
    cA
    wsbc
    #
    wa
    #
    @9
    wb
    #
    @27
    @34
    wb
    #
    @31
    @0
    @32
    @7
    wb
    #
    @33
    @8
    wb
    #
    @35
    @0
    @0
    @37
    @0
    idn1
    #
    @7
    vx
    cA
    cV
    sbcg
    e1a
    @0
    @0
    @38
    @39
    vx
    cA
    @6
    cB
    cV
    sbcel2gOLD
    e1a
    @37
    @38
    @35
    @32
    @33
    @7
    @8
    pm4.38
    ex
    e11
    @0
    @0
    @36
    @39
    @7
    @14
    vx
    cA
    cV
    sbcangOLD
    e1a
    @36
    @31
    @35
    @27
    @34
    @9
    bibi1
    biimprcd
    e11
    gen11
    @27
    @9
    vy
    exbi
    e1a
    @0
    @0
    @30
    @39
    @15
    vy
    vx
    cA
    cV
    sbcexgOLD
    e1a
    @30
    @25
    @29
    @21
    @28
    @10
    bibi1
    biimprcd
    e11
    gen11
    @26
    @23
    @21
    @10
    vz
    abbi
    biimpi
    e1a
    @0
    @0
    @24
    @39
    @16
    vx
    vz
    cA
    cV
    csbabgOLD
    e1a
    @23
    @24
    @19
    @22
    @11
    @18
    eqeq2
    biimpd
    e11
    @0
    @0
    @1
    @17
    wceq
    #
    vx
    cA
    wsbc
    #
    @20
    @39
    @0
    @0
    @40
    vx
    wal
    @41
    @39
    @40
    vx
    vz
    vy
    cB
    df-uni
    ax-gen
    @40
    vx
    cA
    cV
    spsbc
    e10
    @0
    @41
    @20
    vx
    cA
    @1
    @17
    cV
    sbceqg
    biimpd
    e11
    @19
    @20
    @12
    @18
    @11
    @2
    eqeq2
    biimpd
    e11
    vz
    vy
    @3
    df-uni
    @13
    @5
    @12
    @4
    @11
    @2
    eqeq2
    biimprcd
    e10
    in1
end
