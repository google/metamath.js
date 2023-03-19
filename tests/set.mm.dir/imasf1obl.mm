include "cfv.mm"
include "cbl.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wf1o.mm"
include "wceq.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "oveq2d.mm"
include "cimas.mm"
include "adantr.mm"
include "cbs.mm"
include "cxmt.mm"
include "wf.mm"
include "f1ocnv.mm"
include "syl.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "imasdsf1o.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "cxr.mm"
include "wb.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "bitr4d.mm"
include "pm5.32da.mm"
include "imasf1oxmet.mm"
include "ffvelrnd.mm"
include "elbl.mm"
include "syl3anc.mm"
include "wfn.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "3syl.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "imacnvcnv.mm"
include "syl6eq.mm"

theorem imasf1obl
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  assume imasf1obl.u: |- ( ph -> U = ( F "s R ) )
  assume imasf1obl.v: |- ( ph -> V = ( Base ` R ) )
  assume imasf1obl.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasf1obl.r: |- ( ph -> R e. Z )
  assume imasf1obl.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume imasf1obl.d: |- D = ( dist ` U )
  assume imasf1obl.m: |- ( ph -> E e. ( *Met ` V ) )
  assume imasf1obl.x: |- ( ph -> P e. V )
  assume imasf1obl.s: |- ( ph -> S e. RR* )


  assert |- ( ph -> ( ( F ` P ) ( ball ` D ) S ) = ( F " ( P ( ball ` E ) S ) ) )

  proof
    wph
    cP
    cF
    cfv
    #
    cS
    cD
    cbl
    cfv
    co
    #
    cF
    ccnv
    #
    ccnv
    cP
    cS
    cE
    cbl
    cfv
    co
    #
    cima
    #
    cF
    @3
    cima
    wph
    vx
    @1
    @4
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @0
    @5
    cD
    co
    #
    cS
    clt
    wbr
    #
    wa
    #
    @6
    @5
    @2
    cfv
    #
    @3
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    wph
    @6
    @8
    @11
    wph
    @6
    wa
    #
    @8
    cP
    @10
    cE
    co
    #
    cS
    clt
    wbr
    #
    @11
    @15
    @7
    @16
    cS
    clt
    @15
    @0
    @10
    cF
    cfv
    #
    cD
    co
    @7
    @16
    @15
    @18
    @5
    @0
    cD
    wph
    cV
    cB
    cF
    wf1o
    #
    @6
    @18
    @5
    wceq
    imasf1obl.f
    cV
    cB
    @5
    cF
    f1ocnvfv2
    sylan
    oveq2d
    @15
    cB
    cD
    cR
    cU
    cE
    cF
    cV
    cP
    @10
    cZ
    wph
    cU
    cF
    cR
    cimas
    co
    wceq
    @6
    imasf1obl.u
    adantr
    wph
    cV
    cR
    cbs
    cfv
    wceq
    @6
    imasf1obl.v
    adantr
    wph
    @19
    @6
    imasf1obl.f
    adantr
    wph
    cR
    cZ
    wcel
    @6
    imasf1obl.r
    adantr
    imasf1obl.e
    imasf1obl.d
    wph
    cE
    cV
    cxmt
    cfv
    wcel
    #
    @6
    imasf1obl.m
    adantr
    #
    wph
    cP
    cV
    wcel
    #
    @6
    imasf1obl.x
    adantr
    #
    wph
    cB
    cV
    @5
    @2
    wph
    cB
    cV
    @2
    wf1o
    #
    cB
    cV
    @2
    wf
    wph
    @19
    @24
    imasf1obl.f
    cV
    cB
    cF
    f1ocnv
    syl
    #
    cB
    cV
    @2
    f1of
    syl
    ffvelrnda
    #
    imasdsf1o
    eqtr3d
    breq1d
    @15
    @20
    cS
    cxr
    wcel
    #
    @22
    @10
    cV
    wcel
    @11
    @17
    wb
    @21
    wph
    @27
    @6
    imasf1obl.s
    adantr
    @23
    @26
    @10
    cE
    cP
    cS
    cV
    elbl2
    syl22anc
    bitr4d
    pm5.32da
    wph
    cD
    cB
    cxmt
    cfv
    wcel
    @0
    cB
    wcel
    @27
    @13
    @9
    wb
    wph
    cB
    cD
    cR
    cU
    cE
    cF
    cV
    cZ
    imasf1obl.u
    imasf1obl.v
    imasf1obl.f
    imasf1obl.r
    imasf1obl.e
    imasf1obl.d
    imasf1obl.m
    imasf1oxmet
    wph
    cV
    cB
    cP
    cF
    wph
    @19
    cV
    cB
    cF
    wf
    imasf1obl.f
    cV
    cB
    cF
    f1of
    syl
    imasf1obl.x
    ffvelrnd
    imasf1obl.s
    @5
    cD
    @0
    cS
    cB
    elbl
    syl3anc
    wph
    @24
    @2
    cB
    wfn
    @14
    @12
    wb
    @25
    cB
    cV
    @2
    f1ofn
    cB
    @5
    @3
    @2
    elpreima
    3syl
    3bitr4d
    eqrdv
    cF
    @3
    imacnvcnv
    syl6eq
end
