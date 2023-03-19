include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "elfz1end.mm"
include "sylib.mm"
include "snssd.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "elsni.mm"
include "breqan12d.mm"
include "cr.mm"
include "cuz.mm"
include "fzssuz.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "simpr.mm"
include "adantr.mm"
include "sseldi.mm"
include "ltnrd.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "wf.mm"
include "wf1.mm"
include "f1f.mm"
include "syl.mm"
include "wor.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "soisores.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "snidg.mm"
include "eqid.mm"
include "erdszelem1.mm"
include "syl3anbrc.mm"

theorem erdszelem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cK: class K
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let cI: class I
  let cJ: class J
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let cS: class S
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.k: |- K = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.o: |- O Or RR

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O z
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N n
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ( ph /\ A e. ( 1 ... N ) ) -> { A } e. { y e. ~P ( 1 ... A ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ A e. y ) } )

  proof
    wph
    cA
    c1
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    cA
    csn
    #
    c1
    cA
    cfz
    co
    #
    wss
    @3
    cF
    @3
    cima
    clt
    cO
    cF
    @3
    cres
    wiso
    #
    cA
    @3
    wcel
    #
    @3
    vy
    cv
    #
    cF
    @7
    cima
    clt
    cO
    cF
    @7
    cres
    wiso
    cA
    @7
    wcel
    wa
    vy
    @4
    cpw
    crab
    #
    wcel
    @2
    cA
    @4
    @2
    cA
    cn
    wcel
    #
    cA
    @4
    wcel
    @1
    @9
    wph
    cA
    cN
    elfznn
    adantl
    cA
    elfz1end
    sylib
    snssd
    @2
    @5
    vx
    cv
    #
    @7
    clt
    wbr
    #
    @10
    cF
    cfv
    @7
    cF
    cfv
    cO
    wbr
    #
    wi
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    @2
    @13
    vx
    vy
    @3
    @3
    @2
    @10
    @3
    wcel
    #
    @7
    @3
    wcel
    #
    wa
    #
    wa
    #
    @11
    cA
    cA
    clt
    wbr
    #
    @12
    @17
    @11
    @19
    wb
    @2
    @15
    @16
    @10
    cA
    @7
    cA
    clt
    @10
    cA
    elsni
    @7
    cA
    elsni
    breqan12d
    adantl
    @18
    @19
    @12
    @18
    cA
    @18
    @0
    cr
    cA
    @0
    c1
    cuz
    cfv
    #
    cr
    c1
    cN
    fzssuz
    @20
    cz
    cr
    c1
    uzssz
    zssre
    sstri
    sstri
    #
    @2
    @1
    @17
    wph
    @1
    simpr
    #
    adantr
    sseldi
    ltnrd
    pm2.21d
    sylbid
    ralrimivva
    @2
    @0
    cr
    cF
    wf
    #
    @3
    @0
    wss
    #
    @5
    @14
    wb
    #
    wph
    @23
    @1
    wph
    @0
    cr
    cF
    wf1
    @23
    erdsze.f
    @0
    cr
    cF
    f1f
    syl
    adantr
    @2
    cA
    @0
    @22
    snssd
    @0
    clt
    wor
    #
    cr
    cO
    wor
    @23
    @24
    wa
    @25
    @0
    cr
    wss
    cr
    clt
    wor
    @26
    @21
    ltso
    @0
    cr
    clt
    soss
    mp2
    erdszelem.o
    vx
    vy
    @3
    @0
    cr
    clt
    cO
    cF
    soisores
    mpanl12
    syl2anc
    mpbird
    @1
    @6
    wph
    cA
    @0
    snidg
    adantl
    vy
    cA
    @8
    cF
    cO
    @3
    @8
    eqid
    erdszelem1
    syl3anbrc
end
