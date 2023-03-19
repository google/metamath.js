include "cc0.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cibl.mm"
include "cc.mm"
include "wf.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cr.mm"
include "cfz.mm"
include "cmap.mm"
include "wcel.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpld.mm"
include "oveq12d.mm"
include "feq2d.mm"
include "mpbird.mm"
include "feqmptd.mm"
include "nfv.mm"
include "0zd.mm"
include "cuz.mm"
include "nnuz.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "elfzofz.mm"
include "adantl.mm"
include "fzofzp1.mm"
include "cioo.mm"
include "cres.mm"
include "ccncf.mm"
include "ioossicc.mm"
include "cxr.mm"
include "fourierdlem11.mm"
include "simp1d.mm"
include "rexrd.mm"
include "simp2d.mm"
include "fourierdlem15.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "feqresmpt.mm"
include "eqeltrrd.mm"
include "climc.mm"
include "oveq1d.mm"
include "iblcncfioo.mm"
include "sselda.mm"
include "ibliooicc.mm"
include "iblspltprt.mm"
include "eqeltrd.mm"

theorem fourierdlem69
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cL: class L
  let cM: class M
  let vp: setvar p
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem69.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem69.m: |- ( ph -> M e. NN )
  assume fourierdlem69.q: |- ( ph -> Q e. ( P ` M ) )
  assume fourierdlem69.f: |- ( ph -> F : ( A [,] B ) --> CC )
  assume fourierdlem69.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) e. ( ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem69.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` i ) ) )
  assume fourierdlem69.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( Q ` i ) (,) ( Q ` ( i + 1 ) ) ) ) limCC ( Q ` ( i + 1 ) ) ) )

  disjoint A i
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B i
  disjoint B m
  disjoint B p
  disjoint F i
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint Q i
  disjoint Q p
  disjoint i ph
  disjoint A x
  disjoint i x
  disjoint B x
  disjoint F x
  disjoint M x
  disjoint Q x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. L^1 )

  proof
    wph
    cF
    vx
    cc0
    cQ
    cfv
    #
    cM
    cQ
    cfv
    #
    cicc
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    cibl
    wph
    vx
    @2
    cc
    cF
    wph
    @2
    cc
    cF
    wf
    cA
    cB
    cicc
    co
    #
    cc
    cF
    wf
    #
    fourierdlem69.f
    wph
    @2
    @5
    cc
    cF
    wph
    @0
    cA
    @1
    cB
    cicc
    wph
    @0
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wph
    @7
    @8
    wa
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @10
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wph
    cQ
    cr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    wcel
    #
    @9
    @16
    wa
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @18
    @19
    wa
    #
    fourierdlem69.q
    wph
    cM
    cn
    wcel
    @20
    @21
    wb
    fourierdlem69.m
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem69.p
    fourierdlem2
    syl
    mpbid
    #
    simprd
    #
    simpld
    #
    simpld
    #
    wph
    @7
    @8
    @24
    simprd
    #
    oveq12d
    feq2d
    mpbird
    feqmptd
    wph
    vx
    @4
    cQ
    vi
    cc0
    cM
    wph
    vx
    nfv
    wph
    0zd
    wph
    cM
    cn
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    fourierdlem69.m
    cn
    c1
    cuz
    cfv
    @28
    nnuz
    c1
    @27
    cuz
    1e0p1
    fveq2i
    eqtri
    syl6eleq
    wph
    @17
    cr
    @10
    cQ
    wph
    @18
    @17
    cr
    cQ
    wf
    #
    wph
    @18
    @19
    @22
    simpld
    cQ
    cr
    @17
    elmapi
    syl
    #
    ffvelrnda
    wph
    @14
    vi
    @15
    wph
    @9
    @16
    @23
    simprd
    r19.21bi
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @5
    cc
    @3
    cF
    wph
    @6
    @31
    fourierdlem69.f
    adantr
    @32
    @3
    @2
    @5
    wph
    @31
    simpr
    @32
    @0
    cA
    @1
    cB
    cicc
    wph
    @7
    @31
    @25
    adantr
    wph
    @8
    @31
    @26
    adantr
    oveq12d
    eleqtrd
    ffvelrnd
    wph
    @10
    @15
    wcel
    #
    wa
    #
    vx
    @11
    @13
    @4
    @34
    @17
    cr
    @10
    cQ
    wph
    @29
    @33
    @30
    adantr
    #
    @33
    @10
    @17
    wcel
    wph
    @10
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    #
    @34
    @17
    cr
    @12
    cQ
    @35
    @33
    @12
    @17
    wcel
    wph
    cc0
    cM
    @10
    fzofzp1
    adantl
    ffvelrnd
    #
    @34
    @11
    @13
    cR
    vx
    @11
    @13
    cioo
    co
    #
    @4
    cmpt
    #
    cL
    @36
    @37
    @34
    cF
    @38
    cres
    #
    @39
    @38
    cc
    ccncf
    co
    @34
    vx
    @5
    cc
    @38
    cF
    wph
    @6
    @33
    fourierdlem69.f
    adantr
    #
    @34
    @38
    @11
    @13
    cicc
    co
    #
    @5
    @11
    @13
    ioossicc
    @34
    cA
    cB
    cQ
    @10
    cM
    wph
    cA
    cxr
    wcel
    @33
    wph
    cA
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem69.p
    fourierdlem69.m
    fourierdlem69.q
    fourierdlem11
    #
    simp1d
    rexrd
    adantr
    wph
    cB
    cxr
    wcel
    @33
    wph
    cB
    wph
    @43
    @44
    @45
    @46
    simp2d
    rexrd
    adantr
    wph
    @17
    @5
    cQ
    wf
    @33
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem69.p
    fourierdlem69.m
    fourierdlem69.q
    fourierdlem15
    adantr
    wph
    @33
    simpr
    fourierdlem8
    #
    syl5ss
    feqresmpt
    #
    fourierdlem69.fcn
    eqeltrrd
    @34
    cL
    @40
    @13
    climc
    co
    @39
    @13
    climc
    co
    fourierdlem69.l
    @34
    @40
    @39
    @13
    climc
    @48
    oveq1d
    eleqtrd
    @34
    cR
    @40
    @11
    climc
    co
    @39
    @11
    climc
    co
    fourierdlem69.r
    @34
    @40
    @39
    @11
    climc
    @48
    oveq1d
    eleqtrd
    iblcncfioo
    @34
    @3
    @42
    wcel
    #
    wa
    @5
    cc
    @3
    cF
    @34
    @6
    @49
    @41
    adantr
    @34
    @42
    @5
    @3
    @47
    sselda
    ffvelrnd
    ibliooicc
    iblspltprt
    eqeltrd
end
