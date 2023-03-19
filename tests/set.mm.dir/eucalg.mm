include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1st.mm"
include "cgcd.mm"
include "cc0.mm"
include "co.mm"
include "c2nd.mm"
include "cop.mm"
include "cxp.mm"
include "wceq.mm"
include "wf.mm"
include "nn0uz.mm"
include "0zd.mm"
include "opelxpi.mm"
include "syl5eqel.mm"
include "eucalgf.mm"
include "a1i.mm"
include "algrf.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "fveq2i.mm"
include "op2ndg.mm"
include "syl5eq.mm"
include "cuz.mm"
include "cz.mm"
include "xp2nd.mm"
include "nn0zd.mm"
include "uzid.mm"
include "eqid.mm"
include "eucalgcvga.mm"
include "mpd.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "xp1st.mm"
include "nn0gcdid0.mm"
include "3syl.mm"
include "3eqtrrd.mm"
include "cres.mm"
include "wfn.mm"
include "wss.mm"
include "gcdf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "nn0ssz.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fnssres.mm"
include "cv.mm"
include "eucalginv.mm"
include "ffvelrni.mm"
include "fvres.mm"
include "3eqtr4d.mm"
include "alginv.mm"
include "0nn0.mm"
include "sylancl.mm"
include "3eqtr3d.mm"
include "algr0.mm"
include "syl6eq.mm"
include "3eqtrd.mm"

theorem eucalg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cE: class E
  let cM: class M
  let cN: class N
  let cX: class X
  let vz: setvar z
  assume eucalgval.1: |- E = ( x e. NN0 , y e. NN0 |-> if ( y = 0 , <. x , y >. , <. y , ( x mod y ) >. ) )
  assume eucalg.2: |- R = seq 0 ( ( E o. 1st ) , ( NN0 X. { A } ) )
  assume eucalg.3: |- A = <. M , N >.

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint R z
  disjoint E z
  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( 1st ` ( R ` N ) ) = ( M gcd N ) )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cR
    cfv
    #
    c1st
    cfv
    #
    @3
    cgcd
    cfv
    #
    cc0
    cR
    cfv
    #
    cgcd
    cfv
    #
    cM
    cN
    cgcd
    co
    #
    @2
    @5
    @4
    @3
    c2nd
    cfv
    #
    cgcd
    co
    #
    @4
    cc0
    cgcd
    co
    #
    @4
    @2
    @5
    @4
    @9
    cop
    #
    cgcd
    cfv
    @10
    @2
    @3
    @12
    cgcd
    @2
    @3
    cn0
    cn0
    cxp
    #
    wcel
    #
    @3
    @12
    wceq
    @0
    @1
    cn0
    @13
    cR
    wf
    #
    @14
    @2
    cA
    cR
    @13
    cE
    cc0
    cn0
    nn0uz
    eucalg.2
    @2
    0zd
    #
    @2
    cA
    cM
    cN
    cop
    #
    @13
    eucalg.3
    cM
    cN
    cn0
    cn0
    opelxpi
    syl5eqel
    #
    @13
    @13
    cE
    wf
    @2
    vx
    vy
    cE
    eucalgval.1
    eucalgf
    #
    a1i
    algrf
    #
    cn0
    @13
    cN
    cR
    ffvelrn
    sylancom
    #
    @3
    cn0
    cn0
    1st2nd2
    syl
    fveq2d
    @4
    @9
    cgcd
    df-ov
    syl6eqr
    @2
    @9
    cc0
    @4
    cgcd
    @2
    cA
    c2nd
    cfv
    #
    cR
    cfv
    #
    c2nd
    cfv
    #
    @9
    cc0
    @2
    @23
    @3
    c2nd
    @2
    @22
    cN
    cR
    @2
    @22
    @17
    c2nd
    cfv
    cN
    cA
    @17
    c2nd
    eucalg.3
    fveq2i
    cM
    cN
    cn0
    cn0
    op2ndg
    syl5eq
    fveq2d
    fveq2d
    @2
    cA
    @13
    wcel
    #
    @24
    cc0
    wceq
    #
    @18
    @25
    @22
    @22
    cuz
    cfv
    wcel
    #
    @26
    @25
    @22
    cz
    wcel
    @27
    @25
    @22
    cA
    cn0
    cn0
    xp2nd
    nn0zd
    @22
    uzid
    syl
    vx
    vy
    cA
    cR
    cE
    @22
    @22
    eucalgval.1
    eucalg.2
    @22
    eqid
    eucalgcvga
    mpd
    syl
    eqtr3d
    oveq2d
    @2
    @14
    @4
    cn0
    wcel
    @11
    @4
    wceq
    @21
    @3
    cn0
    cn0
    xp1st
    @4
    nn0gcdid0
    3syl
    3eqtrrd
    @2
    @3
    cgcd
    @13
    cres
    #
    cfv
    #
    @6
    @28
    cfv
    #
    @5
    @7
    @0
    @1
    @25
    @29
    @30
    wceq
    @18
    vz
    cA
    cR
    @13
    cE
    @28
    cN
    eucalg.2
    @19
    cgcd
    cz
    cz
    cxp
    #
    wfn
    #
    @13
    @31
    wss
    #
    @28
    @13
    wfn
    @31
    cn0
    cgcd
    wf
    @32
    gcdf
    @31
    cn0
    cgcd
    ffn
    ax-mp
    cn0
    cz
    wss
    #
    @34
    @33
    nn0ssz
    nn0ssz
    cn0
    cz
    cn0
    cz
    xpss12
    mp2an
    @31
    @13
    cgcd
    fnssres
    mp2an
    vz
    cv
    #
    @13
    wcel
    #
    @35
    cE
    cfv
    #
    cgcd
    cfv
    #
    @35
    cgcd
    cfv
    @37
    @28
    cfv
    #
    @35
    @28
    cfv
    vx
    vy
    cE
    @35
    eucalgval.1
    eucalginv
    @36
    @37
    @13
    wcel
    @39
    @38
    wceq
    @13
    @13
    @35
    cE
    @19
    ffvelrni
    @37
    @13
    cgcd
    fvres
    syl
    @35
    @13
    cgcd
    fvres
    3eqtr4d
    alginv
    sylancom
    @2
    @14
    @29
    @5
    wceq
    @21
    @3
    @13
    cgcd
    fvres
    syl
    @2
    @6
    @13
    wcel
    #
    @30
    @7
    wceq
    @2
    @15
    cc0
    cn0
    wcel
    @40
    @20
    0nn0
    cn0
    @13
    cc0
    cR
    ffvelrn
    sylancl
    @6
    @13
    cgcd
    fvres
    syl
    3eqtr3d
    @2
    @7
    @17
    cgcd
    cfv
    @8
    @2
    @6
    @17
    cgcd
    @2
    @6
    cA
    @17
    @2
    cA
    cR
    @13
    cE
    cc0
    cn0
    nn0uz
    eucalg.2
    @16
    @18
    algr0
    eucalg.3
    syl6eq
    fveq2d
    cM
    cN
    cgcd
    df-ov
    syl6eqr
    3eqtrd
end
