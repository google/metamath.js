include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cioo.mm"
include "cdm.mm"
include "wss.mm"
include "cc.mm"
include "ccncf.mm"
include "cres.mm"
include "wral.mm"
include "wn.mm"
include "simplr.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "simplll.mm"
include "ioossicc.mm"
include "cxr.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "a1i.mm"
include "cfz.mm"
include "wf.mm"
include "fourierdlem15.mm"
include "adantr.mm"
include "simpr.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "sselda.mm"
include "simpllr.mm"
include "w3a.mm"
include "cn.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "cun.mm"
include "crn.mm"
include "simp2.mm"
include "simp3.mm"
include "eldifd.mm"
include "elun2.mm"
include "syl.mm"
include "wceq.mm"
include "syl6req.mm"
include "eleqtrd.mm"
include "fourierdlem12.mm"
include "syl31anc.mm"
include "condan.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "rescncf.mm"
include "sylc.mm"

theorem fourierdlem38
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cM: class M
  let vp: setvar p
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem38.cn: |- ( ph -> F e. ( dom F -cn-> CC ) )
  assume fourierdlem38.p: |- P = ( n e. NN |-> { p e. ( RR ^m ( 0 ... n ) ) | ( ( ( p ` 0 ) = -u _pi /\ ( p ` n ) = _pi ) /\ A. i e. ( 0 ..^ n ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem38.m: |- ( ph -> M e. NN )
  assume fourierdlem38.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem38.h: |- H = ( A u. ( ( -u _pi [,] _pi ) \ dom F ) )
  assume fourierdlem38.ranq: |- ( ph -> ran Q = H )

  disjoint F i
  disjoint M i
  disjoint M n
  disjoint M p
  disjoint i n
  disjoint i p
  disjoint n p
  disjoint Q i
  disjoint Q p
  disjoint i ph
  disjoint F x
  disjoint i x
  disjoint M x
  disjoint Q x
  disjoint ph x
  disjoint k x
  assert |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )

  proof
    wph
    vi
    cv
    #
    cc0
    cM
    cfzo
    co
    wcel
    #
    wa
    #
    @0
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    cQ
    cfv
    #
    cioo
    co
    #
    cF
    cdm
    #
    wss
    #
    cF
    @6
    cc
    ccncf
    co
    wcel
    #
    cF
    @5
    cres
    @5
    cc
    ccncf
    co
    wcel
    @2
    vx
    cv
    #
    @6
    wcel
    #
    vx
    @5
    wral
    @7
    @2
    @10
    vx
    @5
    @2
    @9
    @5
    wcel
    #
    wa
    #
    @10
    @11
    @2
    @11
    @10
    wn
    #
    simplr
    @12
    @13
    wa
    wph
    @9
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    #
    @13
    @1
    @11
    wn
    wph
    @1
    @11
    @13
    simplll
    @12
    @16
    @13
    @2
    @5
    @15
    @9
    @2
    @5
    @3
    @4
    cicc
    co
    @15
    @3
    @4
    ioossicc
    @2
    @14
    cpi
    cQ
    @0
    cM
    @14
    cxr
    wcel
    @2
    @14
    cpi
    pire
    renegcli
    rexri
    a1i
    cpi
    cxr
    wcel
    @2
    cpi
    pire
    rexri
    a1i
    wph
    cc0
    cM
    cfz
    co
    @15
    cQ
    wf
    @1
    wph
    @14
    cpi
    cP
    cQ
    vi
    vn
    cM
    vp
    fourierdlem38.p
    fourierdlem38.m
    fourierdlem38.q
    fourierdlem15
    adantr
    wph
    @1
    simpr
    fourierdlem8
    syl5ss
    sselda
    adantr
    @12
    @13
    simpr
    wph
    @1
    @11
    @13
    simpllr
    wph
    @16
    @13
    w3a
    #
    @14
    cpi
    cP
    cQ
    vi
    vn
    cM
    @9
    vp
    fourierdlem38.p
    wph
    @16
    cM
    cn
    wcel
    @13
    fourierdlem38.m
    3ad2ant1
    wph
    @16
    cQ
    cM
    cP
    cfv
    wcel
    @13
    fourierdlem38.q
    3ad2ant1
    @17
    @9
    cA
    @15
    @6
    cdif
    #
    cun
    #
    cQ
    crn
    #
    @17
    @9
    @18
    wcel
    @9
    @19
    wcel
    @17
    @9
    @15
    @6
    wph
    @16
    @13
    simp2
    wph
    @16
    @13
    simp3
    eldifd
    @9
    @18
    cA
    elun2
    syl
    wph
    @16
    @19
    @20
    wceq
    @13
    wph
    @20
    cH
    @19
    fourierdlem38.ranq
    fourierdlem38.h
    syl6req
    3ad2ant1
    eleqtrd
    fourierdlem12
    syl31anc
    condan
    ralrimiva
    vx
    @5
    @6
    dfss3
    sylibr
    wph
    @8
    @1
    fourierdlem38.cn
    adantr
    @6
    cc
    @5
    cF
    rescncf
    sylc
end
