include "cc0.mm"
include "cfv.mm"
include "cseq.mm"
include "c1.mm"
include "cop.mm"
include "fveq1i.mm"
include "0z.mm"
include "csn.mm"
include "cn0.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "cn.mm"
include "dfn2.mm"
include "reseq2i.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "syl5reqr.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "c0ex.mm"
include "opex.mm"
include "eqid.mm"
include "fvsnun1.mm"
include "syl6eq.mm"
include "seq1i.mm"

theorem ruclem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let vm: setvar m
  let cF: class F
  let cG: class G
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vn: setvar n
  let vk: setvar k
  let cM: class M
  let cN: class N
  let cS: class S
  assume ruc.1: |- ( ph -> F : NN --> RR )
  assume ruc.2: |- ( ph -> D = ( x e. ( RR X. RR ) , y e. RR |-> [_ ( ( ( 1st ` x ) + ( 2nd ` x ) ) / 2 ) / m ]_ if ( m < y , <. ( 1st ` x ) , m >. , <. ( ( m + ( 2nd ` x ) ) / 2 ) , ( 2nd ` x ) >. ) ) )
  assume ruc.4: |- C = ( { <. 0 , <. 0 , 1 >. >. } u. F )
  assume ruc.5: |- G = seq 0 ( D , C )

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G x
  disjoint G y
  disjoint m w
  disjoint w x
  disjoint w y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint w z
  disjoint C w
  disjoint C z
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G n
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N k
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint k w
  disjoint k ph
  disjoint n w
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D w
  disjoint D z
  disjoint S n
  disjoint S z
  assert |- ( ph -> ( G ` 0 ) = <. 0 , 1 >. )

  proof
    wph
    cc0
    cG
    cfv
    cc0
    cD
    cC
    cc0
    cseq
    #
    cfv
    cc0
    c1
    cop
    #
    cc0
    cG
    @0
    ruc.5
    fveq1i
    wph
    @1
    cD
    cC
    cc0
    0z
    wph
    cc0
    cC
    cfv
    cc0
    cc0
    @1
    cop
    csn
    #
    cF
    cn0
    cc0
    csn
    cdif
    #
    cres
    #
    cun
    #
    cfv
    @1
    wph
    cc0
    cC
    @5
    wph
    cC
    @2
    cF
    cun
    @5
    ruc.4
    wph
    cF
    @4
    @2
    wph
    @4
    cF
    cn
    cres
    #
    cF
    cn
    @3
    cF
    dfn2
    reseq2i
    wph
    cn
    cr
    cF
    wf
    cF
    cn
    wfn
    @6
    cF
    wceq
    ruc.1
    cn
    cr
    cF
    ffn
    cn
    cF
    fnresdm
    3syl
    syl5reqr
    uneq2d
    syl5eq
    fveq1d
    cc0
    @1
    cn0
    cF
    @5
    c0ex
    cc0
    c1
    opex
    @5
    eqid
    fvsnun1
    syl6eq
    seq1i
    syl5eq
end
