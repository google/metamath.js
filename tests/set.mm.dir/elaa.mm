include "caa.mm"
include "wcel.mm"
include "cz.mm"
include "cply.mm"
include "cfv.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "ccnv.mm"
include "cc0.mm"
include "cima.mm"
include "ciun.mm"
include "cc.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "df-aa.mm"
include "eleq2i.mm"
include "eliun.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eldifi.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "4syl.mm"
include "rexbiia.mm"
include "r19.42v.mm"
include "bitri.mm"

theorem elaa
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R

  disjoint A f
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B z
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint f i
  disjoint f j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F z
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint R f
  disjoint R k
  disjoint R m
  disjoint R z
  assert |- ( A e. AA <-> ( A e. CC /\ E. f e. ( ( Poly ` ZZ ) \ { 0p } ) ( f ` A ) = 0 ) )

  proof
    cA
    caa
    wcel
    cA
    vf
    cz
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    vf
    cv
    #
    ccnv
    cc0
    csn
    cima
    #
    ciun
    #
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    @3
    cfv
    cc0
    wceq
    #
    vf
    @2
    wrex
    wa
    #
    caa
    @5
    cA
    vf
    df-aa
    eleq2i
    @6
    cA
    @4
    wcel
    #
    vf
    @2
    wrex
    #
    @9
    vf
    cA
    @2
    @4
    eliun
    @11
    @7
    @8
    wa
    #
    vf
    @2
    wrex
    @9
    @10
    @12
    vf
    @2
    @3
    @2
    wcel
    @3
    @0
    wcel
    cc
    cc
    @3
    wf
    @3
    cc
    wfn
    @10
    @12
    wb
    @3
    @0
    @1
    eldifi
    cz
    @3
    plyf
    cc
    cc
    @3
    ffn
    cc
    cc0
    cA
    @3
    fniniseg
    4syl
    rexbiia
    @7
    @8
    vf
    @2
    r19.42v
    bitri
    bitri
    bitri
end
