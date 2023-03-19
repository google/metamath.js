include "csn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "csb.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "fveq1d.mm"
include "adantr.mm"
include "snssd.mm"
include "sselda.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "1ex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"
include "elsni.mm"
include "iftrued.mm"
include "adantl.mm"
include "oveq1d.mm"
include "cc.mm"
include "syldan.mm"
include "mulid2d.mm"
include "sumeq2dv.mm"
include "ax-1cn.mm"
include "0cn.mm"
include "keepel.mm"
include "syl6eqel.mm"
include "mulcld.mm"
include "cdif.mm"
include "eldifi.mm"
include "eldifn.mm"
include "velsn.mm"
include "sylnib.mm"
include "iffalsed.mm"
include "mul02d.mm"
include "fsumss.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "csbeq1a.mm"
include "chvar.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "mpdan.mm"
include "sumsns.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem flcidc
  let wph: wff ph
  let cB: class B
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cK: class K
  assume flcidc.f: |- ( ph -> F = ( j e. S |-> if ( j = K , 1 , 0 ) ) )
  assume flcidc.s: |- ( ph -> S e. Fin )
  assume flcidc.k: |- ( ph -> K e. S )
  assume flcidc.b: |- ( ( ph /\ i e. S ) -> B e. CC )

  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint F i
  disjoint S i
  disjoint S j
  disjoint K i
  disjoint K j
  disjoint B j
  assert |- ( ph -> sum_ i e. S ( ( F ` i ) x. B ) = [_ K / i ]_ B )

  proof
    wph
    cK
    csn
    #
    vi
    cv
    #
    cF
    cfv
    #
    cB
    cmul
    co
    #
    vi
    csu
    @0
    cB
    vi
    csu
    #
    cS
    @3
    vi
    csu
    vi
    cK
    cB
    csb
    #
    wph
    @0
    @3
    cB
    vi
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    c1
    cB
    cmul
    co
    cB
    @7
    @2
    c1
    cB
    cmul
    @7
    @2
    @1
    cK
    wceq
    #
    c1
    cc0
    cif
    #
    c1
    @7
    @2
    @1
    vj
    cS
    vj
    cv
    #
    cK
    wceq
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    @9
    wph
    @2
    @14
    wceq
    #
    @6
    wph
    @1
    cF
    @13
    flcidc.f
    fveq1d
    #
    adantr
    @7
    @1
    cS
    wcel
    #
    @14
    @9
    wceq
    #
    wph
    @0
    cS
    @1
    wph
    cK
    cS
    flcidc.k
    snssd
    #
    sselda
    #
    vj
    @1
    @12
    @9
    cS
    @13
    @10
    @1
    wceq
    @11
    @8
    c1
    cc0
    @10
    @1
    cK
    eqeq1
    ifbid
    @13
    eqid
    @8
    c1
    cc0
    1ex
    c0ex
    ifex
    fvmpt
    #
    syl
    eqtrd
    #
    @6
    @9
    c1
    wceq
    wph
    @6
    @8
    c1
    cc0
    @1
    cK
    elsni
    iftrued
    adantl
    eqtrd
    oveq1d
    @7
    cB
    wph
    @6
    @17
    cB
    cc
    wcel
    #
    @20
    flcidc.b
    syldan
    #
    mulid2d
    eqtrd
    sumeq2dv
    wph
    @0
    cS
    @3
    vi
    @19
    @7
    @2
    cB
    @7
    @2
    @9
    cc
    @22
    @8
    c1
    cc0
    cc
    ax-1cn
    0cn
    keepel
    syl6eqel
    @24
    mulcld
    wph
    @1
    cS
    @0
    cdif
    wcel
    #
    wa
    #
    @3
    cc0
    cB
    cmul
    co
    cc0
    @26
    @2
    cc0
    cB
    cmul
    @26
    @2
    @9
    cc0
    @26
    @2
    @14
    @9
    wph
    @15
    @25
    @16
    adantr
    @26
    @17
    @18
    @25
    @17
    wph
    @1
    cS
    @0
    eldifi
    adantl
    #
    @21
    syl
    eqtrd
    @25
    @9
    cc0
    wceq
    wph
    @25
    @8
    c1
    cc0
    @25
    @6
    @8
    @1
    cS
    @0
    eldifn
    vi
    cK
    velsn
    sylnib
    iffalsed
    adantl
    eqtrd
    oveq1d
    @26
    cB
    wph
    @25
    @17
    @23
    @27
    flcidc.b
    syldan
    mul02d
    eqtrd
    flcidc.s
    fsumss
    wph
    cK
    cS
    wcel
    #
    @5
    cc
    wcel
    #
    @4
    @5
    wceq
    flcidc.k
    wph
    @28
    @29
    flcidc.k
    wph
    @28
    @29
    wph
    @10
    cS
    wcel
    #
    wa
    #
    vi
    @10
    cB
    csb
    #
    cc
    wcel
    #
    wi
    #
    wph
    @28
    wa
    #
    @29
    wi
    vj
    cK
    cS
    @11
    @31
    @35
    @33
    @29
    @11
    @30
    @28
    wph
    @10
    cK
    cS
    eleq1
    anbi2d
    @11
    @32
    @5
    cc
    vi
    @10
    cK
    cB
    csbeq1
    eleq1d
    imbi12d
    wph
    @17
    wa
    #
    @23
    wi
    @34
    vi
    vj
    @31
    @33
    vi
    @31
    vi
    nfv
    vi
    @32
    cc
    vi
    @10
    cB
    nfcsb1v
    nfel1
    nfim
    @1
    @10
    wceq
    #
    @36
    @31
    @23
    @33
    @37
    @17
    @30
    wph
    @1
    @10
    cS
    eleq1
    anbi2d
    @37
    cB
    @32
    cc
    vi
    @10
    cB
    csbeq1a
    eleq1d
    imbi12d
    flcidc.b
    chvar
    vtoclg
    anabsi7
    mpdan
    cB
    vi
    cK
    cS
    sumsns
    syl2anc
    3eqtr3d
end
