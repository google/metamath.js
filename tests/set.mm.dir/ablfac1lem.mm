include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "cpc.mm"
include "cexp.mm"
include "cprime.mm"
include "sselda.mm"
include "prmnn.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "cabl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "grpbn0.mm"
include "3syl.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "adantr.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "syl5eqel.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "pcdvds.mm"
include "syl2anc.mm"
include "syl5eqbr.mm"
include "nndivdvds.mm"
include "mpbid.mm"
include "jca.mm"
include "oveq1i.mm"
include "wn.mm"
include "pcndvds2.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "breq2i.mm"
include "sylnibr.mm"
include "cz.mm"
include "nnzd.mm"
include "coprm.mm"
include "cn0.mm"
include "wi.mm"
include "prmz.mm"
include "rpexp1i.mm"
include "syl3anc.mm"
include "mpd.mm"
include "syl5eq.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "syl5req.mm"
include "3jca.mm"

theorem ablfac1lem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vq: setvar q
  let vw: setvar w
  let vy: setvar y
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cT: class T
  assume ablfac1.b: |- B = ( Base ` G )
  assume ablfac1.o: |- O = ( od ` G )
  assume ablfac1.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac1.g: |- ( ph -> G e. Abel )
  assume ablfac1.f: |- ( ph -> B e. Fin )
  assume ablfac1.1: |- ( ph -> A C_ Prime )
  assume ablfac1.m: |- M = ( P ^ ( P pCnt ( # ` B ) ) )
  assume ablfac1.n: |- N = ( ( # ` B ) / M )

  disjoint p x
  disjoint B p
  disjoint B x
  disjoint p ph
  disjoint ph x
  disjoint A p
  disjoint A x
  disjoint O p
  disjoint O x
  disjoint P p
  disjoint P x
  disjoint G p
  disjoint G x
  disjoint p q
  disjoint p w
  disjoint p y
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint B q
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B y
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint q z
  disjoint ph q
  disjoint w z
  disjoint ph w
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint S q
  disjoint A a
  disjoint A b
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint O q
  disjoint O y
  disjoint P q
  disjoint P y
  disjoint P z
  disjoint T q
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint G a
  disjoint G b
  disjoint G q
  disjoint G y
  disjoint G z
  assert |- ( ( ph /\ P e. A ) -> ( ( M e. NN /\ N e. NN ) /\ ( M gcd N ) = 1 /\ ( # ` B ) = ( M x. N ) ) )

  proof
    wph
    cP
    cA
    wcel
    #
    wa
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    cM
    cN
    cgcd
    co
    #
    c1
    wceq
    cB
    chash
    cfv
    #
    cM
    cN
    cmul
    co
    #
    wceq
    @1
    @2
    @3
    @1
    cM
    cP
    cP
    @5
    cpc
    co
    #
    cexp
    co
    #
    cn
    ablfac1.m
    @1
    cP
    @7
    @1
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    wph
    cA
    cprime
    cP
    ablfac1.1
    sselda
    #
    cP
    prmnn
    syl
    @1
    cP
    @5
    @10
    wph
    @5
    cn
    wcel
    #
    @0
    wph
    @11
    cB
    c0
    wne
    #
    wph
    cG
    cabl
    wcel
    cG
    cgrp
    wcel
    @12
    ablfac1.g
    cG
    ablgrp
    cB
    cG
    ablfac1.b
    grpbn0
    3syl
    wph
    cB
    cfn
    wcel
    @11
    @12
    wb
    ablfac1.f
    cB
    hashnncl
    syl
    mpbird
    adantr
    #
    pccld
    #
    nnexpcld
    syl5eqel
    #
    @1
    cN
    @5
    cM
    cdiv
    co
    #
    cn
    ablfac1.n
    @1
    cM
    @5
    cdvds
    wbr
    #
    @16
    cn
    wcel
    #
    @1
    cM
    @8
    @5
    cdvds
    ablfac1.m
    @1
    @9
    @11
    @8
    @5
    cdvds
    wbr
    @10
    @13
    cP
    @5
    pcdvds
    syl2anc
    syl5eqbr
    @1
    @11
    @2
    @17
    @18
    wb
    @13
    @15
    @5
    cM
    nndivdvds
    syl2anc
    mpbid
    syl5eqel
    #
    jca
    @1
    @4
    @8
    cN
    cgcd
    co
    #
    c1
    cM
    @8
    cN
    cgcd
    ablfac1.m
    oveq1i
    @1
    cP
    cN
    cgcd
    co
    c1
    wceq
    #
    @20
    c1
    wceq
    #
    @1
    cP
    cN
    cdvds
    wbr
    #
    wn
    #
    @21
    @1
    cP
    @5
    @8
    cdiv
    co
    #
    cdvds
    wbr
    #
    @23
    @1
    @9
    @11
    @26
    wn
    @10
    @13
    cP
    @5
    pcndvds2
    syl2anc
    cN
    @25
    cP
    cdvds
    cN
    @16
    @25
    ablfac1.n
    cM
    @8
    @5
    cdiv
    ablfac1.m
    oveq2i
    eqtri
    breq2i
    sylnibr
    @1
    @9
    cN
    cz
    wcel
    #
    @24
    @21
    wb
    @10
    @1
    cN
    @19
    nnzd
    #
    cP
    cN
    coprm
    syl2anc
    mpbid
    @1
    cP
    cz
    wcel
    #
    @27
    @7
    cn0
    wcel
    @21
    @22
    wi
    @1
    @9
    @29
    @10
    cP
    prmz
    syl
    @28
    @14
    cP
    cN
    @7
    rpexp1i
    syl3anc
    mpd
    syl5eq
    @1
    @6
    cM
    @16
    cmul
    co
    @5
    cN
    @16
    cM
    cmul
    ablfac1.n
    oveq2i
    @1
    @5
    cM
    @1
    @5
    @13
    nncnd
    @1
    cM
    @15
    nncnd
    @1
    cM
    @15
    nnne0d
    divcan2d
    syl5req
    3jca
end
