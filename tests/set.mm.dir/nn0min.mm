include "wn.mm"
include "wa.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cn.mm"
include "adantr.mm"
include "wsb.mm"
include "c1.mm"
include "wsbc.mm"
include "cv.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfim.mm"
include "wceq.mm"
include "dfsbcq2.mm"
include "notbid.mm"
include "imbi2d.mm"
include "sbhypf.mm"
include "caddc.mm"
include "co.mm"
include "sbequ12r.mm"
include "cc0.mm"
include "wcel.mm"
include "0nn0.mm"
include "sbie.mm"
include "syl5bbr.mm"
include "wb.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "1nn.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sbcieg.mm"
include "3syl.mm"
include "sbceq1d.mm"
include "bitr3d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "mpan9.mm"
include "cbvralsv.mm"
include "nnnn0.mm"
include "syl.mm"
include "syl5bi.mm"
include "adantld.mm"
include "a2d.mm"
include "nnindf.mm"
include "rgen.mm"
include "r19.21v.mm"
include "mpbi.mm"
include "ralnex.mm"
include "sylib.mm"
include "pm2.65da.mm"
include "imnan.mm"
include "ralbii.mm"
include "sylnib.mm"
include "dfrex2.mm"
include "sylibr.mm"

theorem nn0min
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  assume nn0min.0: |- ( n = 0 -> ( ps <-> ch ) )
  assume nn0min.1: |- ( n = m -> ( ps <-> th ) )
  assume nn0min.2: |- ( n = ( m + 1 ) -> ( ps <-> ta ) )
  assume nn0min.3: |- ( ph -> -. ch )
  assume nn0min.4: |- ( ph -> E. n e. NN ps )

  disjoint m n
  disjoint m ph
  disjoint n ph
  disjoint m ps
  disjoint n ta
  disjoint n th
  disjoint ch m
  disjoint ch n
  disjoint k m
  disjoint k n
  disjoint k ph
  disjoint k ps
  disjoint k ta
  disjoint k th
  assert |- ( ph -> E. m e. NN0 ( -. th /\ ta ) )

  proof
    wph
    wth
    wn
    #
    wta
    wa
    #
    wn
    #
    vm
    cn0
    wral
    #
    wn
    @1
    vm
    cn0
    wrex
    wph
    @0
    wta
    wn
    #
    wi
    #
    vm
    cn0
    wral
    #
    @3
    wph
    @6
    wps
    vn
    cn
    wrex
    #
    wph
    @7
    @6
    nn0min.4
    adantr
    wph
    @6
    wa
    #
    wps
    wn
    #
    vn
    cn
    wral
    #
    @7
    wn
    @8
    @9
    wi
    #
    vn
    cn
    wral
    @8
    @10
    wi
    @11
    vn
    cn
    @8
    wps
    vn
    vk
    wsb
    #
    wn
    #
    wi
    @8
    wps
    vn
    c1
    wsbc
    #
    wn
    #
    wi
    @8
    @0
    wi
    @8
    @4
    wi
    @11
    vk
    vm
    vn
    cv
    #
    @8
    @13
    vm
    wph
    @6
    vm
    wph
    vm
    nfv
    @5
    vm
    cn0
    nfra1
    nfan
    @13
    vm
    nfv
    nfim
    vk
    cv
    #
    c1
    wceq
    #
    @13
    @15
    @8
    @18
    @12
    @14
    wps
    vn
    vk
    c1
    dfsbcq2
    notbid
    imbi2d
    @17
    vm
    cv
    #
    wceq
    #
    @13
    @0
    @8
    @20
    @12
    wth
    wps
    wth
    vn
    vk
    @19
    wth
    vn
    nfv
    #
    nn0min.1
    sbhypf
    notbid
    imbi2d
    @17
    @19
    c1
    caddc
    co
    #
    wceq
    #
    @13
    @4
    @8
    @23
    @12
    wta
    wps
    wta
    vn
    vk
    @22
    wta
    vn
    nfv
    nn0min.2
    sbhypf
    notbid
    imbi2d
    @17
    @16
    wceq
    #
    @13
    @9
    @8
    @24
    @12
    wps
    wps
    vk
    vn
    sbequ12r
    notbid
    imbi2d
    wph
    wch
    wn
    #
    @6
    @15
    nn0min.3
    cc0
    cn0
    wcel
    @6
    @25
    @15
    wi
    #
    wi
    0nn0
    @5
    @26
    vm
    cc0
    cn0
    @19
    cc0
    wceq
    #
    @0
    @25
    @4
    @15
    @27
    wth
    wch
    wth
    wps
    vn
    vm
    wsb
    @27
    wch
    wps
    wth
    vn
    vm
    @21
    nn0min.1
    sbie
    wps
    wch
    vn
    vm
    cc0
    wch
    vn
    nfv
    nn0min.0
    sbhypf
    syl5bbr
    notbid
    @27
    wta
    @14
    @27
    wps
    vn
    @22
    wsbc
    #
    wta
    @14
    @27
    @22
    c1
    wceq
    #
    @22
    cn
    wcel
    #
    @28
    wta
    wb
    @27
    @22
    cc0
    c1
    caddc
    co
    c1
    @19
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    #
    @29
    @30
    c1
    cn
    wcel
    1nn
    @22
    c1
    cn
    eleq1
    mpbiri
    wps
    wta
    vn
    @22
    cn
    nn0min.2
    sbcieg
    3syl
    @27
    wps
    vn
    @22
    c1
    @31
    sbceq1d
    bitr3d
    notbid
    imbi12d
    rspcv
    ax-mp
    mpan9
    @19
    cn
    wcel
    #
    @8
    @0
    @4
    @32
    @6
    @5
    wph
    @6
    @5
    vm
    vk
    wsb
    #
    vk
    cn0
    wral
    #
    @32
    @5
    @5
    vm
    vk
    cn0
    cbvralsv
    @32
    @19
    cn0
    wcel
    @34
    @5
    wi
    @19
    nnnn0
    @33
    @5
    vk
    @19
    cn0
    @5
    vk
    vm
    sbequ12r
    rspcv
    syl
    syl5bi
    adantld
    a2d
    nnindf
    rgen
    @8
    @9
    vn
    cn
    r19.21v
    mpbi
    wps
    vn
    cn
    ralnex
    sylib
    pm2.65da
    @5
    @2
    vm
    cn0
    @0
    wta
    imnan
    ralbii
    sylnib
    @1
    vm
    cn0
    dfrex2
    sylibr
end
