include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cxad.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "infxrcl.mm"
include "syl.mm"
include "id.mm"
include "sseldd.mm"
include "crp.mm"
include "rpxr.mm"
include "xaddcld.mm"
include "cle.mm"
include "wbr.mm"
include "infxrlb.mm"
include "syl2anc.mm"
include "c2.mm"
include "cdiv.mm"
include "sselda.mm"
include "mpdan.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "pnfge.mm"
include "adantr.mm"
include "oveq1.mm"
include "adantl.mm"
include "cmnf.mm"
include "wne.mm"
include "cr.mm"
include "rpre.mm"
include "renemnf.mm"
include "xaddpnf2.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "rphalfcl.mm"
include "rpxrd.mm"
include "xleadd1d.mm"
include "neqne.mm"
include "renepnf.mm"
include "3syl.mm"
include "xaddass2.mm"
include "syl222anc.mm"
include "caddc.mm"
include "rehalfcl.mm"
include "rexaddd.mm"
include "cc.mm"
include "recn.mm"
include "2halves.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "pm2.61dan.mm"
include "xrletrd.mm"

theorem infleinflem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume infleinflem1.a: |- ( ph -> A C_ RR* )
  assume infleinflem1.b: |- ( ph -> B C_ RR* )
  assume infleinflem1.w: |- ( ph -> W e. RR+ )
  assume infleinflem1.x: |- ( ph -> X e. B )
  assume infleinflem1.i: |- ( ph -> X <_ ( inf ( B , RR* , < ) +e ( W / 2 ) ) )
  assume infleinflem1.z: |- ( ph -> Z e. A )
  assume infleinflem1.l: |- ( ph -> Z <_ ( X +e ( W / 2 ) ) )


  assert |- ( ph -> inf ( A , RR* , < ) <_ ( inf ( B , RR* , < ) +e W ) )

  proof
    wph
    cA
    cxr
    clt
    cinf
    #
    cZ
    cB
    cxr
    clt
    cinf
    #
    cW
    cxad
    co
    #
    wph
    @0
    cxr
    wcel
    #
    @3
    wph
    cA
    cxr
    wss
    #
    @3
    infleinflem1.a
    cA
    infxrcl
    syl
    @3
    id
    syl
    wph
    cA
    cxr
    cZ
    infleinflem1.a
    infleinflem1.z
    sseldd
    #
    wph
    @1
    cW
    wph
    cB
    cxr
    wss
    @1
    cxr
    wcel
    #
    infleinflem1.b
    cB
    infxrcl
    syl
    #
    wph
    cW
    crp
    wcel
    #
    cW
    cxr
    wcel
    #
    infleinflem1.w
    cW
    rpxr
    #
    syl
    xaddcld
    #
    wph
    @4
    cZ
    cA
    wcel
    @0
    cZ
    cle
    wbr
    infleinflem1.a
    infleinflem1.z
    cA
    cZ
    infxrlb
    syl2anc
    wph
    cZ
    cX
    cW
    c2
    cdiv
    co
    #
    cxad
    co
    #
    @2
    @5
    wph
    cX
    @12
    wph
    cX
    cB
    wcel
    cX
    cxr
    wcel
    infleinflem1.x
    wph
    cB
    cxr
    cX
    infleinflem1.b
    sselda
    mpdan
    wph
    @12
    wph
    cW
    wph
    cW
    infleinflem1.w
    rpred
    rehalfcld
    rexrd
    #
    xaddcld
    #
    @11
    infleinflem1.l
    wph
    @1
    cpnf
    wceq
    #
    @13
    @2
    cle
    wbr
    wph
    @16
    wa
    #
    @13
    cpnf
    @2
    cle
    wph
    @13
    cpnf
    cle
    wbr
    #
    @16
    wph
    @13
    cxr
    wcel
    @18
    @15
    @13
    pnfge
    syl
    adantr
    @17
    @2
    cpnf
    cW
    cxad
    co
    #
    cpnf
    @16
    @2
    @19
    wceq
    wph
    @1
    cpnf
    cW
    cxad
    oveq1
    adantl
    wph
    @19
    cpnf
    wceq
    #
    @16
    wph
    @8
    @20
    infleinflem1.w
    @8
    @9
    cW
    cmnf
    wne
    #
    @20
    @10
    @8
    cW
    cr
    wcel
    #
    @21
    cW
    rpre
    #
    cW
    renemnf
    syl
    cW
    xaddpnf2
    syl2anc
    syl
    adantr
    eqtr2d
    breqtrd
    wph
    @16
    wn
    #
    wa
    #
    @13
    @1
    @12
    cxad
    co
    #
    @12
    cxad
    co
    #
    @2
    cle
    wph
    @13
    @27
    cle
    wbr
    @24
    wph
    cX
    @26
    @12
    wph
    cB
    cxr
    cX
    infleinflem1.b
    infleinflem1.x
    sseldd
    wph
    @1
    @12
    @7
    @14
    xaddcld
    wph
    @12
    wph
    @8
    @12
    crp
    wcel
    #
    infleinflem1.w
    cW
    rphalfcl
    #
    syl
    rpxrd
    #
    infleinflem1.i
    xleadd1d
    adantr
    @25
    @27
    @1
    @12
    @12
    cxad
    co
    #
    cxad
    co
    #
    @2
    @25
    @6
    @1
    cpnf
    wne
    #
    @12
    cxr
    wcel
    #
    @12
    cpnf
    wne
    #
    @34
    @35
    @27
    @32
    wceq
    wph
    @6
    @24
    @7
    adantr
    @24
    @33
    wph
    @1
    cpnf
    neqne
    adantl
    wph
    @34
    @24
    @30
    adantr
    #
    @25
    @8
    @35
    wph
    @8
    @24
    infleinflem1.w
    adantr
    #
    @8
    @28
    @12
    cr
    wcel
    @35
    @29
    @12
    rpre
    @12
    renepnf
    3syl
    syl
    #
    @36
    @38
    @1
    @12
    @12
    xaddass2
    syl222anc
    @25
    @8
    @22
    @32
    @2
    wceq
    @37
    @23
    @22
    @31
    cW
    @1
    cxad
    @22
    @31
    @12
    @12
    caddc
    co
    #
    cW
    @22
    @12
    @12
    cW
    rehalfcl
    #
    @40
    rexaddd
    @22
    cW
    cc
    wcel
    @39
    cW
    wceq
    cW
    recn
    cW
    2halves
    syl
    eqtrd
    oveq2d
    3syl
    eqtrd
    breqtrd
    pm2.61dan
    xrletrd
    xrletrd
end
