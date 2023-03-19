include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "wb.mm"
include "wcel.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "3bitr4i.mm"
include "a1i.mm"
include "riotabiia.mm"
include "3eqtr4i.mm"

theorem cdleme25cv
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vs: setvar s
  assume cdleme25cv.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme25cv.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ s ) ./\ W ) ) )
  assume cdleme25cv.g: |- G = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme25cv.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ ( ( R .\/ z ) ./\ W ) ) )
  assume cdleme25cv.i: |- I = ( iota_ u e. B A. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme25cv.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )

  disjoint s z
  disjoint A s
  disjoint A z
  disjoint .\/ s
  disjoint .\/ z
  disjoint .<_ s
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ z
  disjoint P s
  disjoint P z
  disjoint Q s
  disjoint Q z
  disjoint R s
  disjoint R z
  disjoint U s
  disjoint U z
  disjoint W s
  disjoint W z
  disjoint s u
  disjoint u z
  assert |- I = E

  proof
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @0
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vu
    cv
    #
    cN
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    vu
    cB
    crio
    vz
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @11
    @3
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @7
    cO
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vu
    cB
    crio
    cI
    cE
    @10
    @19
    vu
    cB
    @10
    @19
    wb
    @7
    cB
    wcel
    @6
    @7
    @3
    @0
    cU
    c.or
    co
    #
    cQ
    cP
    @0
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cR
    @0
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    wi
    #
    vs
    cA
    wral
    @16
    @7
    @3
    @11
    cU
    c.or
    co
    #
    cQ
    cP
    @11
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cR
    @11
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    wi
    #
    vz
    cA
    wral
    @10
    @19
    @30
    @41
    vs
    vz
    cA
    @0
    @11
    wceq
    #
    @6
    @16
    @29
    @40
    @42
    @2
    @13
    @5
    @15
    @42
    @1
    @12
    @0
    @11
    cW
    c.le
    breq1
    notbid
    @42
    @4
    @14
    @0
    @11
    @3
    c.le
    breq1
    notbid
    anbi12d
    @42
    @28
    @39
    @7
    @42
    @27
    @38
    @3
    c.an
    @42
    @24
    @35
    @26
    @37
    c.or
    @42
    @20
    @31
    @23
    @34
    c.an
    @0
    @11
    cU
    c.or
    oveq1
    @42
    @22
    @33
    cQ
    c.or
    @42
    @21
    @32
    cW
    c.an
    @0
    @11
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    @42
    @25
    @36
    cW
    c.an
    @0
    @11
    cR
    c.or
    oveq2
    oveq1d
    oveq12d
    oveq2d
    eqeq2d
    imbi12d
    cbvralv
    @9
    @30
    vs
    cA
    @8
    @29
    @6
    cN
    @28
    @7
    cN
    @3
    cF
    @26
    c.or
    co
    #
    c.an
    co
    @28
    cdleme25cv.n
    @43
    @27
    @3
    c.an
    cF
    @24
    @26
    c.or
    cdleme25cv.f
    oveq1i
    oveq2i
    eqtri
    eqeq2i
    imbi2i
    ralbii
    @18
    @41
    vz
    cA
    @17
    @40
    @16
    cO
    @39
    @7
    cO
    @3
    cG
    @37
    c.or
    co
    #
    c.an
    co
    @39
    cdleme25cv.o
    @44
    @38
    @3
    c.an
    cG
    @35
    @37
    c.or
    cdleme25cv.g
    oveq1i
    oveq2i
    eqtri
    eqeq2i
    imbi2i
    ralbii
    3bitr4i
    a1i
    riotabiia
    cdleme25cv.i
    cdleme25cv.e
    3eqtr4i
end
