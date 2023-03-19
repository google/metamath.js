include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "covol.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "cmnf.mm"
include "wbr.mm"
include "cle.mm"
include "wss.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cn.mm"
include "wf.mm"
include "cxp.mm"
include "cin.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "eqid.mm"
include "ovolsf.mm"
include "syl.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "rpred.mm"
include "readdcld.mm"
include "c1.mm"
include "mnfxr.mm"
include "a1i.mm"
include "wfn.mm"
include "ffn.mm"
include "1nn.mm"
include "fnfvelrn.mm"
include "sylancl.mm"
include "sseldd.mm"
include "rge0ssre.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "mnflt.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "xrltletrd.mm"
include "xrre.mm"
include "syl22anc.mm"

theorem ioombl1lem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ioombl1.b: |- B = ( A (,) +oo )
  assume ioombl1.a: |- ( ph -> A e. RR )
  assume ioombl1.e: |- ( ph -> E C_ RR )
  assume ioombl1.v: |- ( ph -> ( vol* ` E ) e. RR )
  assume ioombl1.c: |- ( ph -> C e. RR+ )
  assume ioombl1.s: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ioombl1.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume ioombl1.u: |- U = seq 1 ( + , ( ( abs o. - ) o. H ) )
  assume ioombl1.f1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ioombl1.f2: |- ( ph -> E C_ U. ran ( (,) o. F ) )
  assume ioombl1.f3: |- ( ph -> sup ( ran S , RR* , < ) <_ ( ( vol* ` E ) + C ) )
  assume ioombl1.p: |- P = ( 1st ` ( F ` n ) )
  assume ioombl1.q: |- Q = ( 2nd ` ( F ` n ) )
  assume ioombl1.g: |- G = ( n e. NN |-> <. if ( if ( P <_ A , A , P ) <_ Q , if ( P <_ A , A , P ) , Q ) , Q >. )
  assume ioombl1.h: |- H = ( n e. NN |-> <. P , if ( if ( P <_ A , A , P ) <_ Q , if ( P <_ A , A , P ) , Q ) >. )

  disjoint B n
  disjoint C n
  disjoint E n
  disjoint F n
  disjoint G n
  disjoint H n
  disjoint n ph
  disjoint S n
  disjoint n x
  disjoint B x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint C j
  disjoint k n
  disjoint k x
  disjoint C k
  disjoint C x
  disjoint E x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint H j
  disjoint H k
  disjoint H x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j z
  disjoint S j
  disjoint k z
  disjoint S k
  disjoint n z
  disjoint x z
  disjoint S x
  disjoint S z
  disjoint T j
  disjoint T x
  disjoint T z
  disjoint U j
  disjoint U x
  disjoint U z
  assert |- ( ph -> sup ( ran S , RR* , < ) e. RR )

  proof
    wph
    cS
    crn
    #
    cxr
    clt
    csup
    #
    cxr
    wcel
    #
    cE
    covol
    cfv
    #
    cC
    caddc
    co
    #
    cr
    wcel
    cmnf
    @1
    clt
    wbr
    @1
    @4
    cle
    wbr
    @1
    cr
    wcel
    wph
    @0
    cxr
    wss
    #
    @2
    wph
    @0
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    @6
    cS
    wf
    #
    @0
    @6
    wss
    wph
    cn
    cle
    cr
    cr
    cxp
    cin
    cF
    wf
    @7
    ioombl1.f1
    cS
    cF
    cabs
    cmin
    ccom
    cF
    ccom
    #
    @8
    eqid
    ioombl1.s
    ovolsf
    syl
    #
    cn
    @6
    cS
    frn
    syl
    cc0
    cpnf
    icossxr
    syl6ss
    #
    @0
    supxrcl
    syl
    #
    wph
    @3
    cC
    ioombl1.v
    wph
    cC
    ioombl1.c
    rpred
    readdcld
    wph
    cmnf
    c1
    cS
    cfv
    #
    @1
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    wph
    @0
    cxr
    @12
    @10
    wph
    cS
    cn
    wfn
    #
    c1
    cn
    wcel
    #
    @12
    @0
    wcel
    #
    wph
    @7
    @13
    @9
    cn
    @6
    cS
    ffn
    syl
    1nn
    cn
    c1
    cS
    fnfvelrn
    sylancl
    #
    sseldd
    @11
    wph
    @12
    cr
    wcel
    cmnf
    @12
    clt
    wbr
    wph
    @6
    cr
    @12
    rge0ssre
    wph
    @7
    @14
    @12
    @6
    wcel
    @9
    1nn
    cn
    @6
    c1
    cS
    ffvelrn
    sylancl
    sseldi
    @12
    mnflt
    syl
    wph
    @5
    @15
    @12
    @1
    cle
    wbr
    @10
    @16
    @0
    @12
    supxrub
    syl2anc
    xrltletrd
    ioombl1.f3
    @1
    @4
    xrre
    syl22anc
end
