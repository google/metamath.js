include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "wbr.mm"
include "wal.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "cnt.mm"
include "climc.mm"
include "c0.mm"
include "noel.mm"
include "a1i.mm"
include "csn.mm"
include "cdif.mm"
include "cc.mm"
include "wss.mm"
include "sstrd.mm"
include "adantr.mm"
include "ssdifssd.mm"
include "cmin.mm"
include "cdiv.mm"
include "wf.mm"
include "dvbss.mm"
include "sselda.mm"
include "dvlem.mm"
include "fmptd.mm"
include "sseldd.mm"
include "cabs.mm"
include "clt.mm"
include "cle.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "unblimceq0.mm"
include "neleqtrrd.mm"
include "intnand.mm"
include "wb.mm"
include "eqid.mm"
include "eldv.mm"
include "notbid.mm"
include "mpbird.mm"
include "alrimiv.mm"
include "wex.mm"
include "simpr.mm"
include "eldmg.mm"
include "syl.mm"
include "alnex.mm"
include "bicomd.mm"
include "bitrd.mm"
include "pm2.01da.mm"

theorem unbdqndv1
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vb: setvar b
  let vd: setvar d
  let vy: setvar y
  assume unbdqndv1.g: |- G = ( z e. ( X \ { A } ) |-> ( ( ( F ` z ) - ( F ` A ) ) / ( z - A ) ) )
  assume unbdqndv1.1: |- ( ph -> S C_ CC )
  assume unbdqndv1.2: |- ( ph -> X C_ S )
  assume unbdqndv1.3: |- ( ph -> F : X --> CC )
  assume unbdqndv1.4: |- ( ph -> A. b e. RR+ A. d e. RR+ E. x e. ( X \ { A } ) ( ( abs ` ( x - A ) ) < d /\ b <_ ( abs ` ( G ` x ) ) ) )

  disjoint A b
  disjoint A d
  disjoint A x
  disjoint b d
  disjoint b x
  disjoint d x
  disjoint A z
  disjoint F b
  disjoint F d
  disjoint F x
  disjoint F z
  disjoint G b
  disjoint G d
  disjoint G x
  disjoint S b
  disjoint S d
  disjoint S x
  disjoint S z
  disjoint X b
  disjoint X d
  disjoint X x
  disjoint X z
  disjoint b ph
  disjoint d ph
  disjoint ph x
  disjoint ph z
  disjoint A y
  disjoint y z
  disjoint F y
  disjoint S y
  disjoint ph y
  assert |- ( ph -> -. A e. dom ( S _D F ) )

  proof
    wph
    cA
    cS
    cF
    cdv
    co
    #
    cdm
    #
    wcel
    #
    wph
    @2
    wa
    #
    @2
    wn
    #
    cA
    vy
    cv
    #
    @0
    wbr
    #
    wn
    #
    vy
    wal
    #
    @3
    @7
    vy
    @3
    @7
    cA
    cX
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    wcel
    #
    @5
    cG
    cA
    climc
    co
    #
    wcel
    #
    wa
    #
    wn
    #
    @3
    @13
    @11
    @3
    @12
    c0
    @5
    @5
    c0
    wcel
    wn
    @3
    @5
    noel
    a1i
    @3
    vx
    cA
    cX
    cA
    csn
    #
    cdif
    #
    cG
    vb
    vd
    @3
    cX
    cc
    @16
    wph
    cX
    cc
    wss
    @2
    wph
    cX
    cS
    cc
    unbdqndv1.2
    unbdqndv1.1
    sstrd
    adantr
    #
    ssdifssd
    @3
    vz
    @17
    vz
    cv
    #
    cF
    cfv
    cA
    cF
    cfv
    cmin
    co
    @19
    cA
    cmin
    co
    cdiv
    co
    cc
    cG
    @3
    @19
    cA
    cX
    cF
    wph
    cX
    cc
    cF
    wf
    @2
    unbdqndv1.3
    adantr
    @18
    wph
    @1
    cX
    cA
    wph
    cX
    cS
    cF
    unbdqndv1.1
    unbdqndv1.3
    unbdqndv1.2
    dvbss
    sselda
    #
    dvlem
    unbdqndv1.g
    fmptd
    @3
    cX
    cc
    cA
    @18
    @20
    sseldd
    wph
    vx
    cv
    #
    cA
    cmin
    co
    cabs
    cfv
    vd
    cv
    clt
    wbr
    vb
    cv
    @21
    cG
    cfv
    cabs
    cfv
    cle
    wbr
    wa
    vx
    @17
    wrex
    vd
    crp
    wral
    vb
    crp
    wral
    @2
    unbdqndv1.4
    adantr
    unblimceq0
    neleqtrrd
    intnand
    wph
    @7
    @15
    wb
    @2
    wph
    @6
    @14
    wph
    vz
    cX
    cA
    @5
    cS
    @10
    cF
    cG
    @9
    @10
    eqid
    @9
    eqid
    unbdqndv1.g
    unbdqndv1.1
    unbdqndv1.3
    unbdqndv1.2
    eldv
    notbid
    adantr
    mpbird
    alrimiv
    @3
    @4
    @6
    vy
    wex
    #
    wn
    #
    @8
    @3
    @2
    @22
    @3
    @2
    @2
    @22
    wb
    wph
    @2
    simpr
    vy
    cA
    @0
    @1
    eldmg
    syl
    notbid
    @3
    @8
    @23
    @8
    @23
    wb
    @3
    @6
    vy
    alnex
    a1i
    bicomd
    bitrd
    mpbird
    pm2.01da
end
